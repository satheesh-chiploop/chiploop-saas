use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const CTRL_OFFSET: usize = 0x00000000;
pub const CTRL_ENABLE_SHIFT: u32 = 0;
pub const CTRL_ENABLE_WIDTH: u32 = 1;
pub const CTRL_ENABLE_MASK: u32 = 0x00000001;
pub const CTRL_ARM_SHIFT: u32 = 1;
pub const CTRL_ARM_WIDTH: u32 = 1;
pub const CTRL_ARM_MASK: u32 = 0x00000002;
pub const CTRL_MODE_SHIFT: u32 = 2;
pub const CTRL_MODE_WIDTH: u32 = 2;
pub const CTRL_MODE_MASK: u32 = 0x0000000C;
pub const CTRL_IRQ_ENABLE_SHIFT: u32 = 4;
pub const CTRL_IRQ_ENABLE_WIDTH: u32 = 4;
pub const CTRL_IRQ_ENABLE_MASK: u32 = 0x000000F0;
pub const VELOCITY_SETPOINT_OFFSET: usize = 0x00000004;
pub const VELOCITY_SETPOINT_VELOCITY_SETPOINT_SHIFT: u32 = 0;
pub const VELOCITY_SETPOINT_VELOCITY_SETPOINT_WIDTH: u32 = 32;
pub const VELOCITY_SETPOINT_VELOCITY_SETPOINT_MASK: u32 = 0xFFFFFFFF;
pub const CLAMP_MIN_OFFSET: usize = 0x00000008;
pub const CLAMP_MIN_CLAMP_MIN_SHIFT: u32 = 0;
pub const CLAMP_MIN_CLAMP_MIN_WIDTH: u32 = 32;
pub const CLAMP_MIN_CLAMP_MIN_MASK: u32 = 0xFFFFFFFF;
pub const CLAMP_MAX_OFFSET: usize = 0x0000000C;
pub const CLAMP_MAX_CLAMP_MAX_SHIFT: u32 = 0;
pub const CLAMP_MAX_CLAMP_MAX_WIDTH: u32 = 32;
pub const CLAMP_MAX_CLAMP_MAX_MASK: u32 = 0xFFFFFFFF;
pub const TIMEOUT_THRESHOLD_OFFSET: usize = 0x00000010;
pub const TIMEOUT_THRESHOLD_TIMEOUT_THRESHOLD_SHIFT: u32 = 0;
pub const TIMEOUT_THRESHOLD_TIMEOUT_THRESHOLD_WIDTH: u32 = 16;
pub const TIMEOUT_THRESHOLD_TIMEOUT_THRESHOLD_MASK: u32 = 0x0000FFFF;
pub const SEQUENCE_COUNTER_OFFSET: usize = 0x00000014;
pub const SEQUENCE_COUNTER_SEQUENCE_COUNTER_SHIFT: u32 = 0;
pub const SEQUENCE_COUNTER_SEQUENCE_COUNTER_WIDTH: u32 = 16;
pub const SEQUENCE_COUNTER_SEQUENCE_COUNTER_MASK: u32 = 0x0000FFFF;
pub const FAULT_CLEAR_W1C_OFFSET: usize = 0x00000018;
pub const FAULT_CLEAR_W1C_FAULT_CLEAR_W1C_SHIFT: u32 = 0;
pub const FAULT_CLEAR_W1C_FAULT_CLEAR_W1C_WIDTH: u32 = 8;
pub const FAULT_CLEAR_W1C_FAULT_CLEAR_W1C_MASK: u32 = 0x000000FF;
pub const STATUS_OFFSET: usize = 0x0000001C;
pub const STATUS_FAULT_STICKY_SHIFT: u32 = 0;
pub const STATUS_FAULT_STICKY_WIDTH: u32 = 8;
pub const STATUS_FAULT_STICKY_MASK: u32 = 0x000000FF;
pub const STATUS_RESPONSE_READY_SHIFT: u32 = 8;
pub const STATUS_RESPONSE_READY_WIDTH: u32 = 1;
pub const STATUS_RESPONSE_READY_MASK: u32 = 0x00000100;
pub const STATUS_FRESH_SHIFT: u32 = 9;
pub const STATUS_FRESH_WIDTH: u32 = 1;
pub const STATUS_FRESH_MASK: u32 = 0x00000200;
pub const STATUS_STALE_SHIFT: u32 = 10;
pub const STATUS_STALE_WIDTH: u32 = 1;
pub const STATUS_STALE_MASK: u32 = 0x00000400;
pub const STATUS_TIMEOUT_SHIFT: u32 = 11;
pub const STATUS_TIMEOUT_WIDTH: u32 = 1;
pub const STATUS_TIMEOUT_MASK: u32 = 0x00000800;
pub const STATUS_LAST_SEEN_SEQUENCE_SHIFT: u32 = 16;
pub const STATUS_LAST_SEEN_SEQUENCE_WIDTH: u32 = 16;
pub const STATUS_LAST_SEEN_SEQUENCE_MASK: u32 = 0xFFFF0000;
pub const ACTUATOR_CMD_OFFSET: usize = 0x00000020;
pub const ACTUATOR_CMD_ACTUATOR_CMD_SHIFT: u32 = 0;
pub const ACTUATOR_CMD_ACTUATOR_CMD_WIDTH: u32 = 32;
pub const ACTUATOR_CMD_ACTUATOR_CMD_MASK: u32 = 0xFFFFFFFF;
pub const IRQ_STATUS_OFFSET: usize = 0x00000024;
pub const IRQ_STATUS_RESPONSE_READY_SHIFT: u32 = 0;
pub const IRQ_STATUS_RESPONSE_READY_WIDTH: u32 = 1;
pub const IRQ_STATUS_RESPONSE_READY_MASK: u32 = 0x00000001;
pub const IRQ_STATUS_STALE_SHIFT: u32 = 1;
pub const IRQ_STATUS_STALE_WIDTH: u32 = 1;
pub const IRQ_STATUS_STALE_MASK: u32 = 0x00000002;
pub const IRQ_STATUS_TIMEOUT_SHIFT: u32 = 2;
pub const IRQ_STATUS_TIMEOUT_WIDTH: u32 = 1;
pub const IRQ_STATUS_TIMEOUT_MASK: u32 = 0x00000004;
pub const IRQ_STATUS_FAULT_SHIFT: u32 = 3;
pub const IRQ_STATUS_FAULT_WIDTH: u32 = 1;
pub const IRQ_STATUS_FAULT_MASK: u32 = 0x00000008;

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
pub fn read_ctrl() -> u32 {
    read_reg(CTRL_OFFSET)
}

#[inline]
pub fn write_ctrl(value: u32) {
    write_reg(CTRL_OFFSET, value)
}

#[inline]
pub fn get_ctrl_enable() -> u32 {
    (read_ctrl() & CTRL_ENABLE_MASK) >> CTRL_ENABLE_SHIFT
}

#[inline]
pub fn set_ctrl_enable(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_ENABLE_MASK) | ((value << CTRL_ENABLE_SHIFT) & CTRL_ENABLE_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_arm() -> u32 {
    (read_ctrl() & CTRL_ARM_MASK) >> CTRL_ARM_SHIFT
}

#[inline]
pub fn set_ctrl_arm(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_ARM_MASK) | ((value << CTRL_ARM_SHIFT) & CTRL_ARM_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_mode() -> u32 {
    (read_ctrl() & CTRL_MODE_MASK) >> CTRL_MODE_SHIFT
}

#[inline]
pub fn set_ctrl_mode(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_MODE_MASK) | ((value << CTRL_MODE_SHIFT) & CTRL_MODE_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_irq_enable() -> u32 {
    (read_ctrl() & CTRL_IRQ_ENABLE_MASK) >> CTRL_IRQ_ENABLE_SHIFT
}

#[inline]
pub fn set_ctrl_irq_enable(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_IRQ_ENABLE_MASK) | ((value << CTRL_IRQ_ENABLE_SHIFT) & CTRL_IRQ_ENABLE_MASK);
    write_ctrl(next);
}

#[inline]
pub fn read_velocity_setpoint() -> u32 {
    read_reg(VELOCITY_SETPOINT_OFFSET)
}

#[inline]
pub fn write_velocity_setpoint(value: u32) {
    write_reg(VELOCITY_SETPOINT_OFFSET, value)
}

#[inline]
pub fn get_velocity_setpoint_velocity_setpoint() -> u32 {
    (read_velocity_setpoint() & VELOCITY_SETPOINT_VELOCITY_SETPOINT_MASK) >> VELOCITY_SETPOINT_VELOCITY_SETPOINT_SHIFT
}

#[inline]
pub fn set_velocity_setpoint_velocity_setpoint(value: u32) {
    let current = read_velocity_setpoint();
    let next = (current & !VELOCITY_SETPOINT_VELOCITY_SETPOINT_MASK) | ((value << VELOCITY_SETPOINT_VELOCITY_SETPOINT_SHIFT) & VELOCITY_SETPOINT_VELOCITY_SETPOINT_MASK);
    write_velocity_setpoint(next);
}

#[inline]
pub fn read_clamp_min() -> u32 {
    read_reg(CLAMP_MIN_OFFSET)
}

#[inline]
pub fn write_clamp_min(value: u32) {
    write_reg(CLAMP_MIN_OFFSET, value)
}

#[inline]
pub fn get_clamp_min_clamp_min() -> u32 {
    (read_clamp_min() & CLAMP_MIN_CLAMP_MIN_MASK) >> CLAMP_MIN_CLAMP_MIN_SHIFT
}

#[inline]
pub fn set_clamp_min_clamp_min(value: u32) {
    let current = read_clamp_min();
    let next = (current & !CLAMP_MIN_CLAMP_MIN_MASK) | ((value << CLAMP_MIN_CLAMP_MIN_SHIFT) & CLAMP_MIN_CLAMP_MIN_MASK);
    write_clamp_min(next);
}

#[inline]
pub fn read_clamp_max() -> u32 {
    read_reg(CLAMP_MAX_OFFSET)
}

#[inline]
pub fn write_clamp_max(value: u32) {
    write_reg(CLAMP_MAX_OFFSET, value)
}

#[inline]
pub fn get_clamp_max_clamp_max() -> u32 {
    (read_clamp_max() & CLAMP_MAX_CLAMP_MAX_MASK) >> CLAMP_MAX_CLAMP_MAX_SHIFT
}

#[inline]
pub fn set_clamp_max_clamp_max(value: u32) {
    let current = read_clamp_max();
    let next = (current & !CLAMP_MAX_CLAMP_MAX_MASK) | ((value << CLAMP_MAX_CLAMP_MAX_SHIFT) & CLAMP_MAX_CLAMP_MAX_MASK);
    write_clamp_max(next);
}

#[inline]
pub fn read_timeout_threshold() -> u32 {
    read_reg(TIMEOUT_THRESHOLD_OFFSET)
}

#[inline]
pub fn write_timeout_threshold(value: u32) {
    write_reg(TIMEOUT_THRESHOLD_OFFSET, value)
}

#[inline]
pub fn get_timeout_threshold_timeout_threshold() -> u32 {
    (read_timeout_threshold() & TIMEOUT_THRESHOLD_TIMEOUT_THRESHOLD_MASK) >> TIMEOUT_THRESHOLD_TIMEOUT_THRESHOLD_SHIFT
}

#[inline]
pub fn set_timeout_threshold_timeout_threshold(value: u32) {
    let current = read_timeout_threshold();
    let next = (current & !TIMEOUT_THRESHOLD_TIMEOUT_THRESHOLD_MASK) | ((value << TIMEOUT_THRESHOLD_TIMEOUT_THRESHOLD_SHIFT) & TIMEOUT_THRESHOLD_TIMEOUT_THRESHOLD_MASK);
    write_timeout_threshold(next);
}

#[inline]
pub fn read_sequence_counter() -> u32 {
    read_reg(SEQUENCE_COUNTER_OFFSET)
}

#[inline]
pub fn write_sequence_counter(value: u32) {
    write_reg(SEQUENCE_COUNTER_OFFSET, value)
}

#[inline]
pub fn get_sequence_counter_sequence_counter() -> u32 {
    (read_sequence_counter() & SEQUENCE_COUNTER_SEQUENCE_COUNTER_MASK) >> SEQUENCE_COUNTER_SEQUENCE_COUNTER_SHIFT
}

#[inline]
pub fn set_sequence_counter_sequence_counter(value: u32) {
    let current = read_sequence_counter();
    let next = (current & !SEQUENCE_COUNTER_SEQUENCE_COUNTER_MASK) | ((value << SEQUENCE_COUNTER_SEQUENCE_COUNTER_SHIFT) & SEQUENCE_COUNTER_SEQUENCE_COUNTER_MASK);
    write_sequence_counter(next);
}

#[inline]
pub fn read_fault_clear_w1c() -> u32 {
    read_reg(FAULT_CLEAR_W1C_OFFSET)
}

#[inline]
pub fn write_fault_clear_w1c(value: u32) {
    write_reg(FAULT_CLEAR_W1C_OFFSET, value)
}

#[inline]
pub fn get_fault_clear_w1c_fault_clear_w1c() -> u32 {
    (read_fault_clear_w1c() & FAULT_CLEAR_W1C_FAULT_CLEAR_W1C_MASK) >> FAULT_CLEAR_W1C_FAULT_CLEAR_W1C_SHIFT
}

#[inline]
pub fn set_fault_clear_w1c_fault_clear_w1c(value: u32) {
    let current = read_fault_clear_w1c();
    let next = (current & !FAULT_CLEAR_W1C_FAULT_CLEAR_W1C_MASK) | ((value << FAULT_CLEAR_W1C_FAULT_CLEAR_W1C_SHIFT) & FAULT_CLEAR_W1C_FAULT_CLEAR_W1C_MASK);
    write_fault_clear_w1c(next);
}

#[inline]
pub fn read_status() -> u32 {
    read_reg(STATUS_OFFSET)
}

#[inline]
pub fn get_status_fault_sticky() -> u32 {
    (read_status() & STATUS_FAULT_STICKY_MASK) >> STATUS_FAULT_STICKY_SHIFT
}

#[inline]
pub fn get_status_response_ready() -> u32 {
    (read_status() & STATUS_RESPONSE_READY_MASK) >> STATUS_RESPONSE_READY_SHIFT
}

#[inline]
pub fn get_status_fresh() -> u32 {
    (read_status() & STATUS_FRESH_MASK) >> STATUS_FRESH_SHIFT
}

#[inline]
pub fn get_status_stale() -> u32 {
    (read_status() & STATUS_STALE_MASK) >> STATUS_STALE_SHIFT
}

#[inline]
pub fn get_status_timeout() -> u32 {
    (read_status() & STATUS_TIMEOUT_MASK) >> STATUS_TIMEOUT_SHIFT
}

#[inline]
pub fn get_status_last_seen_sequence() -> u32 {
    (read_status() & STATUS_LAST_SEEN_SEQUENCE_MASK) >> STATUS_LAST_SEEN_SEQUENCE_SHIFT
}

#[inline]
pub fn read_actuator_cmd() -> u32 {
    read_reg(ACTUATOR_CMD_OFFSET)
}

#[inline]
pub fn get_actuator_cmd_actuator_cmd() -> u32 {
    (read_actuator_cmd() & ACTUATOR_CMD_ACTUATOR_CMD_MASK) >> ACTUATOR_CMD_ACTUATOR_CMD_SHIFT
}

#[inline]
pub fn read_irq_status() -> u32 {
    read_reg(IRQ_STATUS_OFFSET)
}

#[inline]
pub fn get_irq_status_response_ready() -> u32 {
    (read_irq_status() & IRQ_STATUS_RESPONSE_READY_MASK) >> IRQ_STATUS_RESPONSE_READY_SHIFT
}

#[inline]
pub fn get_irq_status_stale() -> u32 {
    (read_irq_status() & IRQ_STATUS_STALE_MASK) >> IRQ_STATUS_STALE_SHIFT
}

#[inline]
pub fn get_irq_status_timeout() -> u32 {
    (read_irq_status() & IRQ_STATUS_TIMEOUT_MASK) >> IRQ_STATUS_TIMEOUT_SHIFT
}

#[inline]
pub fn get_irq_status_fault() -> u32 {
    (read_irq_status() & IRQ_STATUS_FAULT_MASK) >> IRQ_STATUS_FAULT_SHIFT
}

