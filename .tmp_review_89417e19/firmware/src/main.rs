#![no_std]
#![no_main]

mod panic;
pub mod hal;

#[no_mangle]
pub extern "C" fn _start() -> ! {
    let _ = crate::hal::registers::read_control();

    loop {}
}
