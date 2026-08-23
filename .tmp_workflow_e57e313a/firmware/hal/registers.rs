use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const CTRL_OFFSET: usize = 0x00000000;
pub const CTRL_ENABLE_SHIFT: u32 = 0;
pub const CTRL_ENABLE_WIDTH: u32 = 1;
pub const CTRL_ENABLE_MASK: u64 = 0x0000000000000001;
pub const CTRL_SAFE_FALLBACK_SELECT_SHIFT: u32 = 1;
pub const CTRL_SAFE_FALLBACK_SELECT_WIDTH: u32 = 1;
pub const CTRL_SAFE_FALLBACK_SELECT_MASK: u64 = 0x0000000000000002;
pub const MAX_CMD_POS_OFFSET: usize = 0x00000008;
pub const MAX_CMD_POS_MAX_CMD_POS_SHIFT: u32 = 0;
pub const MAX_CMD_POS_MAX_CMD_POS_WIDTH: u32 = 64;
pub const MAX_CMD_POS_MAX_CMD_POS_MASK: u64 = 0xFFFFFFFFFFFFFFFF;
pub const MIN_CMD_POS_OFFSET: usize = 0x00000010;
pub const MIN_CMD_POS_MIN_CMD_POS_SHIFT: u32 = 0;
pub const MIN_CMD_POS_MIN_CMD_POS_WIDTH: u32 = 64;
pub const MIN_CMD_POS_MIN_CMD_POS_MASK: u64 = 0xFFFFFFFFFFFFFFFF;
pub const MAX_CMD_RATE_OFFSET: usize = 0x00000018;
pub const MAX_CMD_RATE_MAX_CMD_RATE_SHIFT: u32 = 0;
pub const MAX_CMD_RATE_MAX_CMD_RATE_WIDTH: u32 = 64;
pub const MAX_CMD_RATE_MAX_CMD_RATE_MASK: u64 = 0xFFFFFFFFFFFFFFFF;
pub const STALE_TIMEOUT_CYCLES_OFFSET: usize = 0x00000020;
pub const STALE_TIMEOUT_CYCLES_STALE_TIMEOUT_CYCLES_SHIFT: u32 = 0;
pub const STALE_TIMEOUT_CYCLES_STALE_TIMEOUT_CYCLES_WIDTH: u32 = 64;
pub const STALE_TIMEOUT_CYCLES_STALE_TIMEOUT_CYCLES_MASK: u64 = 0xFFFFFFFFFFFFFFFF;
pub const RESPONSE_TIMEOUT_CYCLES_OFFSET: usize = 0x00000028;
pub const RESPONSE_TIMEOUT_CYCLES_RESPONSE_TIMEOUT_CYCLES_SHIFT: u32 = 0;
pub const RESPONSE_TIMEOUT_CYCLES_RESPONSE_TIMEOUT_CYCLES_WIDTH: u32 = 64;
pub const RESPONSE_TIMEOUT_CYCLES_RESPONSE_TIMEOUT_CYCLES_MASK: u64 = 0xFFFFFFFFFFFFFFFF;
pub const SEQUENCE_EXPECTED_OFFSET: usize = 0x00000030;
pub const SEQUENCE_EXPECTED_SEQUENCE_EXPECTED_SHIFT: u32 = 0;
pub const SEQUENCE_EXPECTED_SEQUENCE_EXPECTED_WIDTH: u32 = 64;
pub const SEQUENCE_EXPECTED_SEQUENCE_EXPECTED_MASK: u64 = 0xFFFFFFFFFFFFFFFF;
pub const STREAM_VELOCITY_SETPOINT_OFFSET: usize = 0x00000038;
pub const STREAM_VELOCITY_SETPOINT_STREAM_VELOCITY_SETPOINT_SHIFT: u32 = 0;
pub const STREAM_VELOCITY_SETPOINT_STREAM_VELOCITY_SETPOINT_WIDTH: u32 = 64;
pub const STREAM_VELOCITY_SETPOINT_STREAM_VELOCITY_SETPOINT_MASK: u64 = 0xFFFFFFFFFFFFFFFF;
pub const FAULT_MASK_OFFSET: usize = 0x00000040;
pub const FAULT_MASK_FAULT_MASK_SHIFT: u32 = 0;
pub const FAULT_MASK_FAULT_MASK_WIDTH: u32 = 64;
pub const FAULT_MASK_FAULT_MASK_MASK: u64 = 0xFFFFFFFFFFFFFFFF;
pub const STATUS_OFFSET: usize = 0x00000048;
pub const STATUS_BUSY_SHIFT: u32 = 0;
pub const STATUS_BUSY_WIDTH: u32 = 1;
pub const STATUS_BUSY_MASK: u64 = 0x0000000000000001;
pub const STATUS_ACCEPTED_SHIFT: u32 = 1;
pub const STATUS_ACCEPTED_WIDTH: u32 = 1;
pub const STATUS_ACCEPTED_MASK: u64 = 0x0000000000000002;
pub const STATUS_REJECTED_STALE_SHIFT: u32 = 2;
pub const STATUS_REJECTED_STALE_WIDTH: u32 = 1;
pub const STATUS_REJECTED_STALE_MASK: u64 = 0x0000000000000004;
pub const STATUS_REJECTED_SEQ_SHIFT: u32 = 3;
pub const STATUS_REJECTED_SEQ_WIDTH: u32 = 1;
pub const STATUS_REJECTED_SEQ_MASK: u64 = 0x0000000000000008;
pub const STATUS_TIMEOUT_SHIFT: u32 = 4;
pub const STATUS_TIMEOUT_WIDTH: u32 = 1;
pub const STATUS_TIMEOUT_MASK: u64 = 0x0000000000000010;
pub const STATUS_FALLBACK_ACTIVE_SHIFT: u32 = 5;
pub const STATUS_FALLBACK_ACTIVE_WIDTH: u32 = 1;
pub const STATUS_FALLBACK_ACTIVE_MASK: u64 = 0x0000000000000020;
pub const STATUS_CLAMPED_SHIFT: u32 = 6;
pub const STATUS_CLAMPED_WIDTH: u32 = 1;
pub const STATUS_CLAMPED_MASK: u64 = 0x0000000000000040;
pub const STATUS_FAULT_SUMMARY_SHIFT: u32 = 7;
pub const STATUS_FAULT_SUMMARY_WIDTH: u32 = 1;
pub const STATUS_FAULT_SUMMARY_MASK: u64 = 0x0000000000000080;

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
pub fn get_ctrl_safe_fallback_select() -> u64 {
    (read_ctrl() & CTRL_SAFE_FALLBACK_SELECT_MASK) >> CTRL_SAFE_FALLBACK_SELECT_SHIFT
}

#[inline]
pub fn set_ctrl_safe_fallback_select(value: u64) {
    let current = read_ctrl();
    let next = (current & !CTRL_SAFE_FALLBACK_SELECT_MASK) | ((value << CTRL_SAFE_FALLBACK_SELECT_SHIFT) & CTRL_SAFE_FALLBACK_SELECT_MASK);
    write_ctrl(next);
}

#[inline]
pub fn read_max_cmd_pos() -> u64 {
    read_reg(MAX_CMD_POS_OFFSET)
}

#[inline]
pub fn write_max_cmd_pos(value: u64) {
    write_reg(MAX_CMD_POS_OFFSET, value)
}

#[inline]
pub fn get_max_cmd_pos_max_cmd_pos() -> u64 {
    (read_max_cmd_pos() & MAX_CMD_POS_MAX_CMD_POS_MASK) >> MAX_CMD_POS_MAX_CMD_POS_SHIFT
}

#[inline]
pub fn set_max_cmd_pos_max_cmd_pos(value: u64) {
    let current = read_max_cmd_pos();
    let next = (current & !MAX_CMD_POS_MAX_CMD_POS_MASK) | ((value << MAX_CMD_POS_MAX_CMD_POS_SHIFT) & MAX_CMD_POS_MAX_CMD_POS_MASK);
    write_max_cmd_pos(next);
}

#[inline]
pub fn read_min_cmd_pos() -> u64 {
    read_reg(MIN_CMD_POS_OFFSET)
}

#[inline]
pub fn write_min_cmd_pos(value: u64) {
    write_reg(MIN_CMD_POS_OFFSET, value)
}

#[inline]
pub fn get_min_cmd_pos_min_cmd_pos() -> u64 {
    (read_min_cmd_pos() & MIN_CMD_POS_MIN_CMD_POS_MASK) >> MIN_CMD_POS_MIN_CMD_POS_SHIFT
}

#[inline]
pub fn set_min_cmd_pos_min_cmd_pos(value: u64) {
    let current = read_min_cmd_pos();
    let next = (current & !MIN_CMD_POS_MIN_CMD_POS_MASK) | ((value << MIN_CMD_POS_MIN_CMD_POS_SHIFT) & MIN_CMD_POS_MIN_CMD_POS_MASK);
    write_min_cmd_pos(next);
}

#[inline]
pub fn read_max_cmd_rate() -> u64 {
    read_reg(MAX_CMD_RATE_OFFSET)
}

#[inline]
pub fn write_max_cmd_rate(value: u64) {
    write_reg(MAX_CMD_RATE_OFFSET, value)
}

#[inline]
pub fn get_max_cmd_rate_max_cmd_rate() -> u64 {
    (read_max_cmd_rate() & MAX_CMD_RATE_MAX_CMD_RATE_MASK) >> MAX_CMD_RATE_MAX_CMD_RATE_SHIFT
}

#[inline]
pub fn set_max_cmd_rate_max_cmd_rate(value: u64) {
    let current = read_max_cmd_rate();
    let next = (current & !MAX_CMD_RATE_MAX_CMD_RATE_MASK) | ((value << MAX_CMD_RATE_MAX_CMD_RATE_SHIFT) & MAX_CMD_RATE_MAX_CMD_RATE_MASK);
    write_max_cmd_rate(next);
}

#[inline]
pub fn read_stale_timeout_cycles() -> u64 {
    read_reg(STALE_TIMEOUT_CYCLES_OFFSET)
}

#[inline]
pub fn write_stale_timeout_cycles(value: u64) {
    write_reg(STALE_TIMEOUT_CYCLES_OFFSET, value)
}

#[inline]
pub fn get_stale_timeout_cycles_stale_timeout_cycles() -> u64 {
    (read_stale_timeout_cycles() & STALE_TIMEOUT_CYCLES_STALE_TIMEOUT_CYCLES_MASK) >> STALE_TIMEOUT_CYCLES_STALE_TIMEOUT_CYCLES_SHIFT
}

#[inline]
pub fn set_stale_timeout_cycles_stale_timeout_cycles(value: u64) {
    let current = read_stale_timeout_cycles();
    let next = (current & !STALE_TIMEOUT_CYCLES_STALE_TIMEOUT_CYCLES_MASK) | ((value << STALE_TIMEOUT_CYCLES_STALE_TIMEOUT_CYCLES_SHIFT) & STALE_TIMEOUT_CYCLES_STALE_TIMEOUT_CYCLES_MASK);
    write_stale_timeout_cycles(next);
}

#[inline]
pub fn read_response_timeout_cycles() -> u64 {
    read_reg(RESPONSE_TIMEOUT_CYCLES_OFFSET)
}

#[inline]
pub fn write_response_timeout_cycles(value: u64) {
    write_reg(RESPONSE_TIMEOUT_CYCLES_OFFSET, value)
}

#[inline]
pub fn get_response_timeout_cycles_response_timeout_cycles() -> u64 {
    (read_response_timeout_cycles() & RESPONSE_TIMEOUT_CYCLES_RESPONSE_TIMEOUT_CYCLES_MASK) >> RESPONSE_TIMEOUT_CYCLES_RESPONSE_TIMEOUT_CYCLES_SHIFT
}

#[inline]
pub fn set_response_timeout_cycles_response_timeout_cycles(value: u64) {
    let current = read_response_timeout_cycles();
    let next = (current & !RESPONSE_TIMEOUT_CYCLES_RESPONSE_TIMEOUT_CYCLES_MASK) | ((value << RESPONSE_TIMEOUT_CYCLES_RESPONSE_TIMEOUT_CYCLES_SHIFT) & RESPONSE_TIMEOUT_CYCLES_RESPONSE_TIMEOUT_CYCLES_MASK);
    write_response_timeout_cycles(next);
}

#[inline]
pub fn read_sequence_expected() -> u64 {
    read_reg(SEQUENCE_EXPECTED_OFFSET)
}

#[inline]
pub fn write_sequence_expected(value: u64) {
    write_reg(SEQUENCE_EXPECTED_OFFSET, value)
}

#[inline]
pub fn get_sequence_expected_sequence_expected() -> u64 {
    (read_sequence_expected() & SEQUENCE_EXPECTED_SEQUENCE_EXPECTED_MASK) >> SEQUENCE_EXPECTED_SEQUENCE_EXPECTED_SHIFT
}

#[inline]
pub fn set_sequence_expected_sequence_expected(value: u64) {
    let current = read_sequence_expected();
    let next = (current & !SEQUENCE_EXPECTED_SEQUENCE_EXPECTED_MASK) | ((value << SEQUENCE_EXPECTED_SEQUENCE_EXPECTED_SHIFT) & SEQUENCE_EXPECTED_SEQUENCE_EXPECTED_MASK);
    write_sequence_expected(next);
}

#[inline]
pub fn read_stream_velocity_setpoint() -> u64 {
    read_reg(STREAM_VELOCITY_SETPOINT_OFFSET)
}

#[inline]
pub fn write_stream_velocity_setpoint(value: u64) {
    write_reg(STREAM_VELOCITY_SETPOINT_OFFSET, value)
}

#[inline]
pub fn get_stream_velocity_setpoint_stream_velocity_setpoint() -> u64 {
    (read_stream_velocity_setpoint() & STREAM_VELOCITY_SETPOINT_STREAM_VELOCITY_SETPOINT_MASK) >> STREAM_VELOCITY_SETPOINT_STREAM_VELOCITY_SETPOINT_SHIFT
}

#[inline]
pub fn set_stream_velocity_setpoint_stream_velocity_setpoint(value: u64) {
    let current = read_stream_velocity_setpoint();
    let next = (current & !STREAM_VELOCITY_SETPOINT_STREAM_VELOCITY_SETPOINT_MASK) | ((value << STREAM_VELOCITY_SETPOINT_STREAM_VELOCITY_SETPOINT_SHIFT) & STREAM_VELOCITY_SETPOINT_STREAM_VELOCITY_SETPOINT_MASK);
    write_stream_velocity_setpoint(next);
}

#[inline]
pub fn read_fault_mask() -> u64 {
    read_reg(FAULT_MASK_OFFSET)
}

#[inline]
pub fn write_fault_mask(value: u64) {
    write_reg(FAULT_MASK_OFFSET, value)
}

#[inline]
pub fn get_fault_mask_fault_mask() -> u64 {
    (read_fault_mask() & FAULT_MASK_FAULT_MASK_MASK) >> FAULT_MASK_FAULT_MASK_SHIFT
}

#[inline]
pub fn set_fault_mask_fault_mask(value: u64) {
    let current = read_fault_mask();
    let next = (current & !FAULT_MASK_FAULT_MASK_MASK) | ((value << FAULT_MASK_FAULT_MASK_SHIFT) & FAULT_MASK_FAULT_MASK_MASK);
    write_fault_mask(next);
}

#[inline]
pub fn read_status() -> u64 {
    read_reg(STATUS_OFFSET)
}

#[inline]
pub fn get_status_busy() -> u64 {
    (read_status() & STATUS_BUSY_MASK) >> STATUS_BUSY_SHIFT
}

#[inline]
pub fn get_status_accepted() -> u64 {
    (read_status() & STATUS_ACCEPTED_MASK) >> STATUS_ACCEPTED_SHIFT
}

#[inline]
pub fn get_status_rejected_stale() -> u64 {
    (read_status() & STATUS_REJECTED_STALE_MASK) >> STATUS_REJECTED_STALE_SHIFT
}

#[inline]
pub fn get_status_rejected_seq() -> u64 {
    (read_status() & STATUS_REJECTED_SEQ_MASK) >> STATUS_REJECTED_SEQ_SHIFT
}

#[inline]
pub fn get_status_timeout() -> u64 {
    (read_status() & STATUS_TIMEOUT_MASK) >> STATUS_TIMEOUT_SHIFT
}

#[inline]
pub fn get_status_fallback_active() -> u64 {
    (read_status() & STATUS_FALLBACK_ACTIVE_MASK) >> STATUS_FALLBACK_ACTIVE_SHIFT
}

#[inline]
pub fn get_status_clamped() -> u64 {
    (read_status() & STATUS_CLAMPED_MASK) >> STATUS_CLAMPED_SHIFT
}

#[inline]
pub fn get_status_fault_summary() -> u64 {
    (read_status() & STATUS_FAULT_SUMMARY_MASK) >> STATUS_FAULT_SUMMARY_SHIFT
}

