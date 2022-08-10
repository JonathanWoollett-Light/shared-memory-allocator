fn main() {
    #[cfg(not(target_os = "linux"))]
    compile_error!("This library only supports linux")
}
