use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const REVISION_ID_OFFSET: usize = 0x00000000;
pub const REVISION_ID_REVISION_ID_SHIFT: u32 = 0;
pub const REVISION_ID_REVISION_ID_WIDTH: u32 = 16;
pub const REVISION_ID_REVISION_ID_MASK: u64 = 0x000000000000FFFF;
pub const REVISION_ID_RESERVED_SHIFT: u32 = 16;
pub const REVISION_ID_RESERVED_WIDTH: u32 = 48;
pub const REVISION_ID_RESERVED_MASK: u64 = 0xFFFFFFFFFFFF0000;
pub const CTRL_OFFSET: usize = 0x00000004;
pub const CTRL_ENABLE_SHIFT: u32 = 0;
pub const CTRL_ENABLE_WIDTH: u32 = 1;
pub const CTRL_ENABLE_MASK: u64 = 0x0000000000000001;
pub const CTRL_MODE_SHIFT: u32 = 1;
pub const CTRL_MODE_WIDTH: u32 = 3;
pub const CTRL_MODE_MASK: u64 = 0x000000000000000E;
pub const CTRL_SLEW_ENABLE_SHIFT: u32 = 4;
pub const CTRL_SLEW_ENABLE_WIDTH: u32 = 1;
pub const CTRL_SLEW_ENABLE_MASK: u64 = 0x0000000000000010;
pub const CTRL_SAFE_SELECTOR_SHIFT: u32 = 5;
pub const CTRL_SAFE_SELECTOR_WIDTH: u32 = 3;
pub const CTRL_SAFE_SELECTOR_MASK: u64 = 0x00000000000000E0;
pub const CTRL_RESERVED0_SHIFT: u32 = 8;
pub const CTRL_RESERVED0_WIDTH: u32 = 8;
pub const CTRL_RESERVED0_MASK: u64 = 0x000000000000FF00;
pub const CTRL_REQUEST_SEQ_SEED_SHIFT: u32 = 16;
pub const CTRL_REQUEST_SEQ_SEED_WIDTH: u32 = 16;
pub const CTRL_REQUEST_SEQ_SEED_MASK: u64 = 0x00000000FFFF0000;
pub const CTRL_RESPONSE_AGE_LIMIT_SHIFT: u32 = 32;
pub const CTRL_RESPONSE_AGE_LIMIT_WIDTH: u32 = 16;
pub const CTRL_RESPONSE_AGE_LIMIT_MASK: u64 = 0x0000FFFF00000000;
pub const CTRL_TIMEOUT_THRESHOLD_SHIFT: u32 = 48;
pub const CTRL_TIMEOUT_THRESHOLD_WIDTH: u32 = 16;
pub const CTRL_TIMEOUT_THRESHOLD_MASK: u64 = 0xFFFF000000000000;
pub const LIMITS_MIN_OFFSET: usize = 0x00000008;
pub const LIMITS_MIN_ACTUATOR_MIN_SHIFT: u32 = 0;
pub const LIMITS_MIN_ACTUATOR_MIN_WIDTH: u32 = 32;
pub const LIMITS_MIN_ACTUATOR_MIN_MASK: u64 = 0x00000000FFFFFFFF;
pub const LIMITS_MIN_RESERVED_SHIFT: u32 = 32;
pub const LIMITS_MIN_RESERVED_WIDTH: u32 = 32;
pub const LIMITS_MIN_RESERVED_MASK: u64 = 0xFFFFFFFF00000000;
pub const LIMITS_MAX_OFFSET: usize = 0x0000000C;
pub const LIMITS_MAX_ACTUATOR_MAX_SHIFT: u32 = 0;
pub const LIMITS_MAX_ACTUATOR_MAX_WIDTH: u32 = 32;
pub const LIMITS_MAX_ACTUATOR_MAX_MASK: u64 = 0x00000000FFFFFFFF;
pub const LIMITS_MAX_RESERVED_SHIFT: u32 = 32;
pub const LIMITS_MAX_RESERVED_WIDTH: u32 = 32;
pub const LIMITS_MAX_RESERVED_MASK: u64 = 0xFFFFFFFF00000000;
pub const FAULT_STATUS_OFFSET: usize = 0x00000010;
pub const FAULT_STATUS_FAULT_STATUS_SHIFT: u32 = 0;
pub const FAULT_STATUS_FAULT_STATUS_WIDTH: u32 = 1;
pub const FAULT_STATUS_FAULT_STATUS_MASK: u64 = 0x0000000000000001;
pub const FAULT_STATUS_RESERVED0_SHIFT: u32 = 1;
pub const FAULT_STATUS_RESERVED0_WIDTH: u32 = 7;
pub const FAULT_STATUS_RESERVED0_MASK: u64 = 0x00000000000000FE;
pub const FAULT_STATUS_FAULT_CAUSE_SHIFT: u32 = 8;
pub const FAULT_STATUS_FAULT_CAUSE_WIDTH: u32 = 8;
pub const FAULT_STATUS_FAULT_CAUSE_MASK: u64 = 0x000000000000FF00;
pub const FAULT_STATUS_RESERVED1_SHIFT: u32 = 16;
pub const FAULT_STATUS_RESERVED1_WIDTH: u32 = 48;
pub const FAULT_STATUS_RESERVED1_MASK: u64 = 0xFFFFFFFFFFFF0000;
pub const WATCHDOG_SNAPSHOT_OFFSET: usize = 0x00000014;
pub const WATCHDOG_SNAPSHOT_TIMEOUT_COUNTER_SNAPSHOT_SHIFT: u32 = 0;
pub const WATCHDOG_SNAPSHOT_TIMEOUT_COUNTER_SNAPSHOT_WIDTH: u32 = 16;
pub const WATCHDOG_SNAPSHOT_TIMEOUT_COUNTER_SNAPSHOT_MASK: u64 = 0x000000000000FFFF;
pub const WATCHDOG_SNAPSHOT_REQUEST_ID_SNAPSHOT_SHIFT: u32 = 16;
pub const WATCHDOG_SNAPSHOT_REQUEST_ID_SNAPSHOT_WIDTH: u32 = 16;
pub const WATCHDOG_SNAPSHOT_REQUEST_ID_SNAPSHOT_MASK: u64 = 0x00000000FFFF0000;
pub const WATCHDOG_SNAPSHOT_LAST_GOOD_CMD_SHIFT: u32 = 32;
pub const WATCHDOG_SNAPSHOT_LAST_GOOD_CMD_WIDTH: u32 = 32;
pub const WATCHDOG_SNAPSHOT_LAST_GOOD_CMD_MASK: u64 = 0xFFFFFFFF00000000;
pub const STATUS_OFFSET: usize = 0x00000018;
pub const STATUS_SAFE_FALLBACK_SHIFT: u32 = 0;
pub const STATUS_SAFE_FALLBACK_WIDTH: u32 = 1;
pub const STATUS_SAFE_FALLBACK_MASK: u64 = 0x0000000000000001;
pub const STATUS_FAULT_IRQ_SHIFT: u32 = 1;
pub const STATUS_FAULT_IRQ_WIDTH: u32 = 1;
pub const STATUS_FAULT_IRQ_MASK: u64 = 0x0000000000000002;
pub const STATUS_REQUEST_BUSY_SHIFT: u32 = 2;
pub const STATUS_REQUEST_BUSY_WIDTH: u32 = 1;
pub const STATUS_REQUEST_BUSY_MASK: u64 = 0x0000000000000004;
pub const STATUS_VALIDATED_RESPONSE_VALID_SHIFT: u32 = 3;
pub const STATUS_VALIDATED_RESPONSE_VALID_WIDTH: u32 = 1;
pub const STATUS_VALIDATED_RESPONSE_VALID_MASK: u64 = 0x0000000000000008;
pub const STATUS_ACTUATOR_CMD_VALID_SHIFT: u32 = 4;
pub const STATUS_ACTUATOR_CMD_VALID_WIDTH: u32 = 1;
pub const STATUS_ACTUATOR_CMD_VALID_MASK: u64 = 0x0000000000000010;
pub const STATUS_STATUS_SNAPSHOT_VALID_SHIFT: u32 = 5;
pub const STATUS_STATUS_SNAPSHOT_VALID_WIDTH: u32 = 1;
pub const STATUS_STATUS_SNAPSHOT_VALID_MASK: u64 = 0x0000000000000020;
pub const STATUS_RESERVED_SHIFT: u32 = 6;
pub const STATUS_RESERVED_WIDTH: u32 = 58;
pub const STATUS_RESERVED_MASK: u64 = 0xFFFFFFFFFFFFFFC0;
pub const RESERVED_1_OFFSET: usize = 0x0000001C;
pub const RESERVED_1_RESERVED_SHIFT: u32 = 0;
pub const RESERVED_1_RESERVED_WIDTH: u32 = 64;
pub const RESERVED_1_RESERVED_MASK: u64 = 0xFFFFFFFFFFFFFFFF;

#[inline]
fn reg_ptr(offset: usize) -> *mut u64 {
    (BASE_ADDRESS + offset) as *mut u64
}

#[inline]
fn read_reg(offset: usize) -> u64 {
    unsafe { read_volatile(reg_ptr(offset) as *const u64) }
}

#[inline]
fn write_reg(offset: usize, value: u64) {
    unsafe { write_volatile(reg_ptr(offset), value) }
}

#[inline]
pub fn read_revision_id() -> u64 {
    read_reg(REVISION_ID_OFFSET)
}

#[inline]
pub fn get_revision_id_revision_id() -> u64 {
    (read_revision_id() & REVISION_ID_REVISION_ID_MASK) >> REVISION_ID_REVISION_ID_SHIFT
}

#[inline]
pub fn get_revision_id_reserved() -> u64 {
    (read_revision_id() & REVISION_ID_RESERVED_MASK) >> REVISION_ID_RESERVED_SHIFT
}

#[inline]
pub fn read_ctrl() -> u64 {
    read_reg(CTRL_OFFSET)
}

#[inline]
pub fn write_ctrl(value: u64) {
    write_reg(CTRL_OFFSET, value)
}

#[inline]
pub fn get_ctrl_enable() -> u64 {
    (read_ctrl() & CTRL_ENABLE_MASK) >> CTRL_ENABLE_SHIFT
}

#[inline]
pub fn set_ctrl_enable(value: u64) {
    let current = read_ctrl();
    let next = (current & !CTRL_ENABLE_MASK) | ((value << CTRL_ENABLE_SHIFT) & CTRL_ENABLE_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_mode() -> u64 {
    (read_ctrl() & CTRL_MODE_MASK) >> CTRL_MODE_SHIFT
}

#[inline]
pub fn set_ctrl_mode(value: u64) {
    let current = read_ctrl();
    let next = (current & !CTRL_MODE_MASK) | ((value << CTRL_MODE_SHIFT) & CTRL_MODE_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_slew_enable() -> u64 {
    (read_ctrl() & CTRL_SLEW_ENABLE_MASK) >> CTRL_SLEW_ENABLE_SHIFT
}

#[inline]
pub fn set_ctrl_slew_enable(value: u64) {
    let current = read_ctrl();
    let next = (current & !CTRL_SLEW_ENABLE_MASK) | ((value << CTRL_SLEW_ENABLE_SHIFT) & CTRL_SLEW_ENABLE_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_safe_selector() -> u64 {
    (read_ctrl() & CTRL_SAFE_SELECTOR_MASK) >> CTRL_SAFE_SELECTOR_SHIFT
}

#[inline]
pub fn set_ctrl_safe_selector(value: u64) {
    let current = read_ctrl();
    let next = (current & !CTRL_SAFE_SELECTOR_MASK) | ((value << CTRL_SAFE_SELECTOR_SHIFT) & CTRL_SAFE_SELECTOR_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_reserved0() -> u64 {
    (read_ctrl() & CTRL_RESERVED0_MASK) >> CTRL_RESERVED0_SHIFT
}

#[inline]
pub fn get_ctrl_request_seq_seed() -> u64 {
    (read_ctrl() & CTRL_REQUEST_SEQ_SEED_MASK) >> CTRL_REQUEST_SEQ_SEED_SHIFT
}

#[inline]
pub fn set_ctrl_request_seq_seed(value: u64) {
    let current = read_ctrl();
    let next = (current & !CTRL_REQUEST_SEQ_SEED_MASK) | ((value << CTRL_REQUEST_SEQ_SEED_SHIFT) & CTRL_REQUEST_SEQ_SEED_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_response_age_limit() -> u64 {
    (read_ctrl() & CTRL_RESPONSE_AGE_LIMIT_MASK) >> CTRL_RESPONSE_AGE_LIMIT_SHIFT
}

#[inline]
pub fn set_ctrl_response_age_limit(value: u64) {
    let current = read_ctrl();
    let next = (current & !CTRL_RESPONSE_AGE_LIMIT_MASK) | ((value << CTRL_RESPONSE_AGE_LIMIT_SHIFT) & CTRL_RESPONSE_AGE_LIMIT_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_timeout_threshold() -> u64 {
    (read_ctrl() & CTRL_TIMEOUT_THRESHOLD_MASK) >> CTRL_TIMEOUT_THRESHOLD_SHIFT
}

#[inline]
pub fn set_ctrl_timeout_threshold(value: u64) {
    let current = read_ctrl();
    let next = (current & !CTRL_TIMEOUT_THRESHOLD_MASK) | ((value << CTRL_TIMEOUT_THRESHOLD_SHIFT) & CTRL_TIMEOUT_THRESHOLD_MASK);
    write_ctrl(next);
}

#[inline]
pub fn read_limits_min() -> u64 {
    read_reg(LIMITS_MIN_OFFSET)
}

#[inline]
pub fn write_limits_min(value: u64) {
    write_reg(LIMITS_MIN_OFFSET, value)
}

#[inline]
pub fn get_limits_min_actuator_min() -> u64 {
    (read_limits_min() & LIMITS_MIN_ACTUATOR_MIN_MASK) >> LIMITS_MIN_ACTUATOR_MIN_SHIFT
}

#[inline]
pub fn set_limits_min_actuator_min(value: u64) {
    let current = read_limits_min();
    let next = (current & !LIMITS_MIN_ACTUATOR_MIN_MASK) | ((value << LIMITS_MIN_ACTUATOR_MIN_SHIFT) & LIMITS_MIN_ACTUATOR_MIN_MASK);
    write_limits_min(next);
}

#[inline]
pub fn get_limits_min_reserved() -> u64 {
    (read_limits_min() & LIMITS_MIN_RESERVED_MASK) >> LIMITS_MIN_RESERVED_SHIFT
}

#[inline]
pub fn read_limits_max() -> u64 {
    read_reg(LIMITS_MAX_OFFSET)
}

#[inline]
pub fn write_limits_max(value: u64) {
    write_reg(LIMITS_MAX_OFFSET, value)
}

#[inline]
pub fn get_limits_max_actuator_max() -> u64 {
    (read_limits_max() & LIMITS_MAX_ACTUATOR_MAX_MASK) >> LIMITS_MAX_ACTUATOR_MAX_SHIFT
}

#[inline]
pub fn set_limits_max_actuator_max(value: u64) {
    let current = read_limits_max();
    let next = (current & !LIMITS_MAX_ACTUATOR_MAX_MASK) | ((value << LIMITS_MAX_ACTUATOR_MAX_SHIFT) & LIMITS_MAX_ACTUATOR_MAX_MASK);
    write_limits_max(next);
}

#[inline]
pub fn get_limits_max_reserved() -> u64 {
    (read_limits_max() & LIMITS_MAX_RESERVED_MASK) >> LIMITS_MAX_RESERVED_SHIFT
}

#[inline]
pub fn read_fault_status() -> u64 {
    read_reg(FAULT_STATUS_OFFSET)
}

#[inline]
pub fn write_fault_status(value: u64) {
    write_reg(FAULT_STATUS_OFFSET, value)
}

#[inline]
pub fn get_fault_status_fault_status() -> u64 {
    (read_fault_status() & FAULT_STATUS_FAULT_STATUS_MASK) >> FAULT_STATUS_FAULT_STATUS_SHIFT
}

#[inline]
pub fn get_fault_status_reserved0() -> u64 {
    (read_fault_status() & FAULT_STATUS_RESERVED0_MASK) >> FAULT_STATUS_RESERVED0_SHIFT
}

#[inline]
pub fn get_fault_status_fault_cause() -> u64 {
    (read_fault_status() & FAULT_STATUS_FAULT_CAUSE_MASK) >> FAULT_STATUS_FAULT_CAUSE_SHIFT
}

#[inline]
pub fn get_fault_status_reserved1() -> u64 {
    (read_fault_status() & FAULT_STATUS_RESERVED1_MASK) >> FAULT_STATUS_RESERVED1_SHIFT
}

#[inline]
pub fn read_watchdog_snapshot() -> u64 {
    read_reg(WATCHDOG_SNAPSHOT_OFFSET)
}

#[inline]
pub fn get_watchdog_snapshot_timeout_counter_snapshot() -> u64 {
    (read_watchdog_snapshot() & WATCHDOG_SNAPSHOT_TIMEOUT_COUNTER_SNAPSHOT_MASK) >> WATCHDOG_SNAPSHOT_TIMEOUT_COUNTER_SNAPSHOT_SHIFT
}

#[inline]
pub fn get_watchdog_snapshot_request_id_snapshot() -> u64 {
    (read_watchdog_snapshot() & WATCHDOG_SNAPSHOT_REQUEST_ID_SNAPSHOT_MASK) >> WATCHDOG_SNAPSHOT_REQUEST_ID_SNAPSHOT_SHIFT
}

#[inline]
pub fn get_watchdog_snapshot_last_good_cmd() -> u64 {
    (read_watchdog_snapshot() & WATCHDOG_SNAPSHOT_LAST_GOOD_CMD_MASK) >> WATCHDOG_SNAPSHOT_LAST_GOOD_CMD_SHIFT
}

#[inline]
pub fn read_status() -> u64 {
    read_reg(STATUS_OFFSET)
}

#[inline]
pub fn get_status_safe_fallback() -> u64 {
    (read_status() & STATUS_SAFE_FALLBACK_MASK) >> STATUS_SAFE_FALLBACK_SHIFT
}

#[inline]
pub fn get_status_fault_irq() -> u64 {
    (read_status() & STATUS_FAULT_IRQ_MASK) >> STATUS_FAULT_IRQ_SHIFT
}

#[inline]
pub fn get_status_request_busy() -> u64 {
    (read_status() & STATUS_REQUEST_BUSY_MASK) >> STATUS_REQUEST_BUSY_SHIFT
}

#[inline]
pub fn get_status_validated_response_valid() -> u64 {
    (read_status() & STATUS_VALIDATED_RESPONSE_VALID_MASK) >> STATUS_VALIDATED_RESPONSE_VALID_SHIFT
}

#[inline]
pub fn get_status_actuator_cmd_valid() -> u64 {
    (read_status() & STATUS_ACTUATOR_CMD_VALID_MASK) >> STATUS_ACTUATOR_CMD_VALID_SHIFT
}

#[inline]
pub fn get_status_status_snapshot_valid() -> u64 {
    (read_status() & STATUS_STATUS_SNAPSHOT_VALID_MASK) >> STATUS_STATUS_SNAPSHOT_VALID_SHIFT
}

#[inline]
pub fn get_status_reserved() -> u64 {
    (read_status() & STATUS_RESERVED_MASK) >> STATUS_RESERVED_SHIFT
}

#[inline]
pub fn read_reserved_1() -> u64 {
    read_reg(RESERVED_1_OFFSET)
}

#[inline]
pub fn get_reserved_1_reserved() -> u64 {
    (read_reserved_1() & RESERVED_1_RESERVED_MASK) >> RESERVED_1_RESERVED_SHIFT
}

