#![feature(allocator_api)]
#![feature(vec_into_raw_parts)]
#![warn(clippy::pedantic)]
#![allow(incomplete_features)]
#![feature(adt_const_params)]

//! An extremely unsafe experiment in writing a custom allocator to use linux shared memory.

use std::alloc::{AllocError, Layout};
use std::io::{Read, Write};
use std::mem::MaybeUninit;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use std::sync::{Arc, Mutex};

struct InMemoryDescription {
    count: AtomicU8,
    capacity: usize,
    length: RwLock<usize>,
}

use std::sync::RwLock;

/// An allocator implementing [`std::alloc::Allocator`] which allocates items in linux shared
/// memory.
#[derive(Clone)]
pub struct SharedAllocator(usize);

impl SharedAllocator {
    /// Since rust doesn't support static members on structs, we do this.
    #[inline]
    fn shmptr_map() -> Arc<Mutex<Vec<(String, i32, usize, u8)>>> {
        static INIT: AtomicBool = AtomicBool::new(false);
        // Counts instance non-dropped shared allocators in this process pointing to the same shared
        // memory.
        // (file, id, ptr, count)
        static mut SHMPTR_MAP: MaybeUninit<Arc<Mutex<Vec<(String, i32, usize, u8)>>>> =
            MaybeUninit::uninit();
        if !INIT.swap(true, Ordering::SeqCst) {
            unsafe {
                SHMPTR_MAP.write(Arc::new(Mutex::new(Vec::new())));
            }
        }
        unsafe { SHMPTR_MAP.assume_init_ref() }.clone()
    }

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
        let map = Self::shmptr_map();
        let mut guard = map.lock().unwrap();
        if let Some((_, _, shmptr, count)) = guard.iter_mut().find(|(p, ..)| p == shmid_path) {
            *count += 1;
            // Rerturn allocator
            Self(*shmptr)
        } else {
            let first = !std::path::Path::new(shmid_path).exists();
            dbg!(first);
            let full_size = size + std::mem::size_of::<InMemoryDescription>();

            // If the shared memory id file doesn't exist, this is the first process to use this
            // shared memory. Thus we must allocate the shared memory.
            let shmid = if first {
                // Allocate shared memory
                reset_err();
                let shmid = unsafe { libc::shmget(libc::IPC_PRIVATE, full_size, libc::IPC_CREAT) };
                dbg!(shmid);
                check_err();
                // We simply save the shared memory id to a file for now
                let mut shmid_file = std::fs::File::create(shmid_path).unwrap();
                shmid_file.write_all(&shmid.to_ne_bytes()).unwrap();
                shmid
            } else {
                // Gets shared memory id
                let mut shmid_file = std::fs::File::open(shmid_path).unwrap();
                let mut shmid_bytes = [0; 4];
                shmid_file.read_exact(&mut shmid_bytes).unwrap();
                let shmid = i32::from_ne_bytes(shmid_bytes);
                dbg!(shmid);
                shmid
            };

            // Attach shared memory
            reset_err();
            let shared_mem_ptr = unsafe { libc::shmat(shmid, std::ptr::null(), 0) };
            dbg!(shared_mem_ptr);
            check_err();

            // If first allocator for this shared memory, create memory description, else increment
            // proccess count
            if first {
                // Create in-memory memory description
                unsafe {
                    std::ptr::write(
                        shared_mem_ptr.cast::<InMemoryDescription>(),
                        InMemoryDescription {
                            count: AtomicU8::new(1),
                            capacity: size,
                            length: RwLock::new(0usize),
                        },
                    );
                }
            } else {
                // Increment process count
                unsafe {
                    (*shared_mem_ptr.cast::<InMemoryDescription>())
                        .count
                        .fetch_add(1, Ordering::SeqCst);
                }
            }

            // Update allocator map and drop guard
            guard.push((shmid_path.to_string(), shmid, shared_mem_ptr as usize, 1));
            // Rerturn allocator
            Self(shared_mem_ptr as usize)
        }
    }
}
impl Drop for SharedAllocator {
    fn drop(&mut self) {
        let map = Self::shmptr_map();
        let mut guard = map.lock().unwrap();

        let index = guard
            .iter()
            .enumerate()
            .find_map(|(i, (_, _, ptr, _))| if *ptr == self.0 { Some(i) } else { None })
            .unwrap();
        // Decrement number of allocators in this process
        guard[index].2 -= 1;
        // If last allocator in this process
        let last_process_allocator = guard[index].2 == 0;
        if last_process_allocator {
            // Detach shared memory
            reset_err();
            let x = unsafe { libc::shmdt(self.0 as *const libc::c_void) };
            dbg!(x);
            check_err();

            let description = unsafe { &*(self.0 as *mut InMemoryDescription) };
            // Decrement number of processes with allocators
            let last_global_allocator = description.count.fetch_sub(1, Ordering::SeqCst) == 1;
            if last_global_allocator {
                // De-allocate shared memory
                reset_err();
                let x =
                    unsafe { libc::shmctl(guard[index].1, libc::IPC_RMID, std::ptr::null_mut()) };
                dbg!(x);
                check_err();

                // Since the second process closes last this one deletes the file
                std::fs::remove_file(&guard[index].0).unwrap();
            }
        }
    }
}

unsafe impl std::alloc::Allocator for SharedAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        // To allocate memory we need a write lock to the length
        let description = unsafe { &*(self.0 as *mut InMemoryDescription) };
        let mut guard = description.length.write().unwrap();

        if description.capacity - *guard > layout.size() {
            // Alloc memory
            let ptr = *guard as *mut u8;
            let nonnull_ptr = unsafe {
                NonNull::new_unchecked(std::ptr::slice_from_raw_parts_mut(ptr, layout.size()))
            };
            // Increase allocated length
            *guard += layout.size();
            // Return pointer
            Ok(nonnull_ptr)
        } else {
            // TODO Make this `AllocError`
            panic!("can't fit")
        }
    }

    #[allow(clippy::significant_drop_in_scrutinee)]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        // To de-allocate memory we need a write lock to the length
        let description = &*(self.0 as *mut InMemoryDescription);
        let mut guard = description.length.write().unwrap();

        // Shifts all data after the deallcoated item down the memory space by the size of the
        // deallocated item.
        let end = ptr.as_ptr().add(layout.size());
        let following_len = *guard - end as usize;
        let mem_after = std::ptr::slice_from_raw_parts_mut(end, following_len);
        std::ptr::replace(ptr.as_ptr().cast::<&[u8]>(), &*mem_after);
        // Decreases the length
        *guard -= layout.size();
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
