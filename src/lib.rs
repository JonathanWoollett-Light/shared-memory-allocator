#![feature(allocator_api)]
#![feature(vec_into_raw_parts)]
#![warn(clippy::pedantic)]

//! An extremely unsafe experiment in writing a custom allocator to use linux shared memory.

use std::alloc::{AllocError, Layout};
use std::collections::HashMap;
use std::io::{Read, Seek, Write};
use std::mem::MaybeUninit;
use std::ops::Range;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

const COUNTER_SUFFIX: &str = "_count";
type Space = Range<usize>;

// Contains data with infomation regarding state of the shared memory
struct SharedMemoryDescription {
    id: String,
    // Overall address space
    address_space: Space,
    // Free memory spaces
    free: Vec<Space>,
}
impl SharedMemoryDescription {
    fn new(address_space: Space, id: &str) -> Self {
        let temp = address_space.clone();
        Self {
            id: String::from(id),
            address_space,
            free: vec![temp],
        }
    }
}
impl Drop for SharedMemoryDescription {
    fn drop(&mut self) {
        // Detach shared memory
        reset_err();
        let x = unsafe { libc::shmdt(self.address_space.start as *const libc::c_void) };
        dbg!(x);
        check_err();

        // De-crement the count of processes accessing this shared memory
        let mut file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(format!("{}{COUNTER_SUFFIX}", self.id))
            .unwrap();
        let mut count = [u8::default()];
        file.read_exact(&mut count).unwrap();
        file.seek(std::io::SeekFrom::Start(0)).unwrap();
        let new_count = count[0] - 1;

        // Only 1 process needs to tell the OS to de-allocate the shared memory
        if new_count == 0 {
            let mut shmid_file = std::fs::File::open(&self.id).unwrap();
            let mut buf = [0; std::mem::size_of::<i32>()];
            shmid_file.read_exact(&mut buf).unwrap();
            let shmid = i32::from_ne_bytes(buf);

            // De-allocate shared memory
            reset_err();
            let x = unsafe { libc::shmctl(shmid, libc::IPC_RMID, std::ptr::null_mut()) };
            dbg!(x);
            check_err();

            // Since the second process closes last this one deletes the file
            std::fs::remove_file(&self.id).unwrap();
            std::fs::remove_file(format!("{}{COUNTER_SUFFIX}", self.id)).unwrap();
        } else {
            file.write_all(&[new_count]).unwrap();
        }
    }
}
/// An allocator implementing [`std::alloc::Allocator`] which allocates items in linux shared
/// memory.
#[derive(Clone)]
pub struct SharedAllocator(Arc<Mutex<SharedMemoryDescription>>);

impl SharedAllocator {
    /// Construct an alloctor storing the shared memory id in a file at `shmid_path`.
    ///
    /// Constructing multiple allocators with the same `shmid_path` will use the same shared memory.
    ///
    /// After constructing the first allocator of a given `shmid_path` constructing new allocators
    /// with the same `shmid_path` is the same as cloning the original allocator.
    ///
    /// Allocators with the same `shmid_path` across processes access the same memory although are
    /// unaware of the presence of items created with allocators from other processes.
    /// If 2 or more processes are allocating items in the same shared memory it is likely memory
    /// will be corrupted.
    ///
    /// When constructing an allocator with the same `shmid_path` as an existing allocator the value
    /// of `size` will not be used for allocating shared memory but rather attaching shared memory.
    /// As such if the value shoould not be larger than the shared memory initially allocated (by
    /// the first allocator constructed with the `shmid_path`)
    ///
    /// This library does not currently implement a mechanism for communicating the layout of the
    /// shared memory between allocators in different processes.
    /// You have to do this manually, in the example of the simplest use case, 1 process stores a
    /// large object in shared memory, when this process wishes to handoff to a newer process it
    /// sends the address of this object in the shared memory over a
    /// [`std::os::unix::net::UnixDatagram`] to the new process, which can pickup this object more
    /// quickly than if it had to be serialized and sent over a [`std::os::unix::net::UnixStream`]
    /// for example
    ///
    /// # Panics
    ///
    /// For a whole lot of reasons. This is not a production ready library, it is a toy, treat it as
    /// such.
    #[must_use]
    pub fn new(shmid_path: &str, size: usize) -> Self {
        type MemoryDescriptorMap = HashMap<i32, Arc<Mutex<SharedMemoryDescription>>>;
        static mut SHARED_MEMORY_DESCRIPTORS: MaybeUninit<Arc<Mutex<MemoryDescriptorMap>>> =
            MaybeUninit::uninit();
        static SHARED: AtomicBool = AtomicBool::new(false);
        let first = !std::path::Path::new(shmid_path).exists();
        dbg!(first);
        // If the shared memory id file doesn't exist, this is the first process to use this shared
        // memory. Thus we must allocate the shared memory.
        if first {
            // Allocate shared memory
            reset_err();
            let shared_mem_id = unsafe { libc::shmget(libc::IPC_PRIVATE, size, libc::IPC_CREAT) };
            dbg!(shared_mem_id);
            check_err();
            // We simply save the shared memory id to a file for now
            let mut shmid_file = std::fs::File::create(shmid_path).unwrap();
            shmid_file.write_all(&shared_mem_id.to_ne_bytes()).unwrap();

            // We create a counter (like a counter in an Arc) to keep the shared memory alive as
            // long as atleast 1 process is using it.
            let mut count_file =
                std::fs::File::create(&format!("{shmid_path}{COUNTER_SUFFIX}")).unwrap();
            count_file.write_all(&1u8.to_ne_bytes()).unwrap();
        }

        // Gets shared memory id
        let mut shmid_file = std::fs::File::open(shmid_path).unwrap();
        let mut shmid_bytes = [0; 4];
        shmid_file.read_exact(&mut shmid_bytes).unwrap();
        // dbg!(shmid_bytes);
        let shmid = i32::from_ne_bytes(shmid_bytes);
        dbg!(shmid);

        // If first shared allocator
        if SHARED.swap(true, Ordering::SeqCst) {
            unsafe {
                SHARED_MEMORY_DESCRIPTORS.write(Arc::new(Mutex::new(HashMap::new())));
            }
        }

        let map_ref = unsafe { SHARED_MEMORY_DESCRIPTORS.assume_init_mut() };
        let mut guard = map_ref.lock().unwrap();
        // If a shared memory description was found, simply create the allocator pointing to this
        // shared memory.
        if let Some(shared_memory_description) = guard.get(&shmid) {
            Self(shared_memory_description.clone())
        }
        // If the map of memory descriptions doesn't contain one for this shared memory id this is
        // the first `SharedAllocator` instance created for this process, and the first time we are
        // trying to access this shared memory.
        // Thus here we want to attach the shared memory to this process (creating the shared memory
        // desription as we do this).
        else {
            // Attach shared memory
            reset_err();
            let shared_mem_ptr = unsafe { libc::shmat(shmid, std::ptr::null(), 0) };
            dbg!(shared_mem_ptr);
            check_err();
            let addr = shared_mem_ptr as usize;
            // Create memory desicrption
            let shared_memory_description = Arc::new(Mutex::new(SharedMemoryDescription::new(
                addr..addr + size,
                shmid_path,
            )));
            guard.insert(shmid, shared_memory_description.clone());
            // Return allocator
            Self(shared_memory_description)
        }
    }
}

unsafe impl std::alloc::Allocator for SharedAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let mut guard = self.0.lock().unwrap();

        // We find free space large enough
        let space_opt = guard
            .free
            .iter_mut()
            .find(|space| (space.end - space.start) >= layout.size());
        let space = match space_opt {
            Some(x) => x,
            // In the future when a space cannot be found of this size we should defragment the
            // address space to produce a large enough contgious space, after this we should attempt
            // to allocate more shared memory
            None => unimplemented!(),
        };
        // We shrink the space
        assert!(space.end >= space.start + layout.size());
        let addr = space.start;
        space.start += layout.size();

        // We alloc the required memory
        let ptr = addr as *mut u8;
        let nonnull_ptr = unsafe {
            NonNull::new_unchecked(std::ptr::slice_from_raw_parts_mut(ptr, layout.size()))
        };
        Ok(nonnull_ptr)
    }

    #[allow(clippy::significant_drop_in_scrutinee)]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        let mut guard = self.0.lock().unwrap();

        let start = ptr.as_ptr() as usize;
        let end = start + layout.size();

        if guard.free[0].start >= end {
            if guard.free[0].end == start {
                guard.free[0].start = start;
            } else {
                guard.free.insert(0, start..end);
            }
        }
        for i in 1..guard.free.len() {
            if guard.free[i].start >= end {
                match (guard.free[i - 1].end == start, guard.free[i].start == end) {
                    (true, true) => {
                        guard.free[i - 1].end = guard.free[i].end;
                        guard.free.remove(i);
                    }
                    (true, false) => {
                        guard.free[i - 1].end = end;
                    }
                    (false, true) => {
                        guard.free[i].start = start;
                    }
                    (false, false) => {
                        guard.free.insert(i, start..end);
                    }
                }
            }
        }
    }
}

fn reset_err() {
    unsafe { *libc::__errno_location() = 0 };
}
fn check_err() {
    let errno = unsafe { libc::__errno_location() };
    let errno = unsafe { *errno };
    if errno != 0 {
        let string = std::ffi::CString::new("message").unwrap();
        unsafe { libc::perror(string.as_ptr()) };
        panic!("Error occured, error code: {errno}");
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;

    const PAGE_SIZE: usize = 4096; // 4kb
    const SIZE: usize = PAGE_SIZE; // 4mb
    #[test]
    fn main() {
        let shmid_file: &str = "/tmp/shmid";

        let first = !std::path::Path::new(shmid_file).exists();
        dbg!(first);

        #[allow(clippy::same_item_push)]
        if first {
            let shared_allocator = SharedAllocator::new(shmid_file, SIZE);
            let mut x = Vec::<u8, _>::new_in(shared_allocator.clone());
            for _ in 0..10 {
                x.push(7);
            }
            dbg!(x.into_raw_parts());
            let mut y = Vec::<u8, _>::new_in(shared_allocator.clone());
            for _ in 0..20 {
                y.push(69);
            }
            dbg!(y.into_raw_parts());
            let mut z = Vec::<u8, _>::new_in(shared_allocator);
            for _ in 0..5 {
                z.push(220);
            }
            dbg!(z.into_raw_parts());
        }

        std::thread::sleep(Duration::from_secs(20));
    }
}
