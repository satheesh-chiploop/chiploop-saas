use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const CONTROL_OFFSET: usize = 0x00000000;
pub const CONTROL_ENABLE_SHIFT: u32 = 0;
pub const CONTROL_ENABLE_WIDTH: u32 = 1;
pub const CONTROL_ENABLE_MASK: u32 = 0x00000001;
pub const CONTROL_RESERVED_SHIFT: u32 = 1;
pub const CONTROL_RESERVED_WIDTH: u32 = 7;
pub const CONTROL_RESERVED_MASK: u32 = 0x000000FE;
pub const DUTY_CYCLE_OFFSET: usize = 0x00000004;
pub const DUTY_CYCLE_DUTY_CYCLE_SHIFT: u32 = 0;
pub const DUTY_CYCLE_DUTY_CYCLE_WIDTH: u32 = 8;
pub const DUTY_CYCLE_DUTY_CYCLE_MASK: u32 = 0x000000FF;
pub const PERIOD_OFFSET: usize = 0x00000008;
pub const PERIOD_PERIOD_SHIFT: u32 = 0;
pub const PERIOD_PERIOD_WIDTH: u32 = 8;
pub const PERIOD_PERIOD_MASK: u32 = 0x000000FF;
pub const COUNTER_VALUE_OFFSET: usize = 0x0000000C;
pub const COUNTER_VALUE_COUNTER_VALUE_SHIFT: u32 = 0;
pub const COUNTER_VALUE_COUNTER_VALUE_WIDTH: u32 = 8;
pub const COUNTER_VALUE_COUNTER_VALUE_MASK: u32 = 0x000000FF;

#[inline]
fn reg_ptr(offset: usize) -> *mut u32 {
    (BASE_ADDRESS + offset) as *mut u32
}

#[inline]
fn read_reg(offset: usize) -> u32 {
    unsafe { read_volatile(reg_ptr(offset) as *const u32) }
}

#[inline]
fn write_reg(offset: usize, value: u32) {
    unsafe { write_volatile(reg_ptr(offset), value) }
}

#[inline]
pub fn read_control() -> u32 {
    read_reg(CONTROL_OFFSET)
}

#[inline]
pub fn write_control(value: u32) {
    write_reg(CONTROL_OFFSET, value)
}

#[inline]
pub fn get_control_enable() -> u32 {
    (read_control() & CONTROL_ENABLE_MASK) >> CONTROL_ENABLE_SHIFT
}

#[inline]
pub fn set_control_enable(value: u32) {
    let current = read_control();
    let next = (current & !CONTROL_ENABLE_MASK) | ((value << CONTROL_ENABLE_SHIFT) & CONTROL_ENABLE_MASK);
    write_control(next);
}

#[inline]
pub fn get_control_reserved() -> u32 {
    (read_control() & CONTROL_RESERVED_MASK) >> CONTROL_RESERVED_SHIFT
}

#[inline]
pub fn read_duty_cycle() -> u32 {
    read_reg(DUTY_CYCLE_OFFSET)
}

#[inline]
pub fn write_duty_cycle(value: u32) {
    write_reg(DUTY_CYCLE_OFFSET, value)
}

#[inline]
pub fn get_duty_cycle_duty_cycle() -> u32 {
    (read_duty_cycle() & DUTY_CYCLE_DUTY_CYCLE_MASK) >> DUTY_CYCLE_DUTY_CYCLE_SHIFT
}

#[inline]
pub fn set_duty_cycle_duty_cycle(value: u32) {
    let current = read_duty_cycle();
    let next = (current & !DUTY_CYCLE_DUTY_CYCLE_MASK) | ((value << DUTY_CYCLE_DUTY_CYCLE_SHIFT) & DUTY_CYCLE_DUTY_CYCLE_MASK);
    write_duty_cycle(next);
}

#[inline]
pub fn read_period() -> u32 {
    read_reg(PERIOD_OFFSET)
}

#[inline]
pub fn write_period(value: u32) {
    write_reg(PERIOD_OFFSET, value)
}

#[inline]
pub fn get_period_period() -> u32 {
    (read_period() & PERIOD_PERIOD_MASK) >> PERIOD_PERIOD_SHIFT
}

#[inline]
pub fn set_period_period(value: u32) {
    let current = read_period();
    let next = (current & !PERIOD_PERIOD_MASK) | ((value << PERIOD_PERIOD_SHIFT) & PERIOD_PERIOD_MASK);
    write_period(next);
}

#[inline]
pub fn read_counter_value() -> u32 {
    read_reg(COUNTER_VALUE_OFFSET)
}

#[inline]
pub fn get_counter_value_counter_value() -> u32 {
    (read_counter_value() & COUNTER_VALUE_COUNTER_VALUE_MASK) >> COUNTER_VALUE_COUNTER_VALUE_SHIFT
}

