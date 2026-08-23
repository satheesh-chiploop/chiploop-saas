use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const CTRL_OFFSET: usize = 0x00000000;
pub const CTRL_ENABLE_SHIFT: u32 = 0;
pub const CTRL_ENABLE_WIDTH: u32 = 1;
pub const CTRL_ENABLE_MASK: u32 = 0x00000001;
pub const CTRL_MODE_SEL_SHIFT: u32 = 1;
pub const CTRL_MODE_SEL_WIDTH: u32 = 2;
pub const CTRL_MODE_SEL_MASK: u32 = 0x00000006;
pub const CTRL_RESERVED_ERROR_EN_SHIFT: u32 = 8;
pub const CTRL_RESERVED_ERROR_EN_WIDTH: u32 = 1;
pub const CTRL_RESERVED_ERROR_EN_MASK: u32 = 0x00000100;
pub const RESERVED_OFFSET: usize = 0x00000000;
pub const RESERVED_RESERVED_ERROR_FLAG_SHIFT: u32 = 0;
pub const RESERVED_RESERVED_ERROR_FLAG_WIDTH: u32 = 1;
pub const RESERVED_RESERVED_ERROR_FLAG_MASK: u32 = 0x00000001;
pub const ENV_LIMIT_OFFSET: usize = 0x00000004;
pub const ENV_LIMIT_ENV_LIMIT_SHIFT: u32 = 0;
pub const ENV_LIMIT_ENV_LIMIT_WIDTH: u32 = 16;
pub const ENV_LIMIT_ENV_LIMIT_MASK: u32 = 0x0000FFFF;
pub const STALE_TIMEOUT_OFFSET: usize = 0x00000008;
pub const STALE_TIMEOUT_STALE_TIMEOUT_SHIFT: u32 = 0;
pub const STALE_TIMEOUT_STALE_TIMEOUT_WIDTH: u32 = 16;
pub const STALE_TIMEOUT_STALE_TIMEOUT_MASK: u32 = 0x0000FFFF;
pub const SEQ_BASE_OFFSET: usize = 0x0000000C;
pub const SEQ_BASE_SEQ_BASE_SHIFT: u32 = 0;
pub const SEQ_BASE_SEQ_BASE_WIDTH: u32 = 16;
pub const SEQ_BASE_SEQ_BASE_MASK: u32 = 0x0000FFFF;
pub const HEARTBEAT_TIMEOUT_OFFSET: usize = 0x00000010;
pub const HEARTBEAT_TIMEOUT_HEARTBEAT_TIMEOUT_SHIFT: u32 = 0;
pub const HEARTBEAT_TIMEOUT_HEARTBEAT_TIMEOUT_WIDTH: u32 = 16;
pub const HEARTBEAT_TIMEOUT_HEARTBEAT_TIMEOUT_MASK: u32 = 0x0000FFFF;
pub const ACT_CLAMP_MIN_OFFSET: usize = 0x00000014;
pub const ACT_CLAMP_MIN_ACT_MIN_SHIFT: u32 = 0;
pub const ACT_CLAMP_MIN_ACT_MIN_WIDTH: u32 = 16;
pub const ACT_CLAMP_MIN_ACT_MIN_MASK: u32 = 0x0000FFFF;
pub const ACT_CLAMP_MAX_OFFSET: usize = 0x00000018;
pub const ACT_CLAMP_MAX_ACT_MAX_SHIFT: u32 = 0;
pub const ACT_CLAMP_MAX_ACT_MAX_WIDTH: u32 = 16;
pub const ACT_CLAMP_MAX_ACT_MAX_MASK: u32 = 0x0000FFFF;
pub const RATE_LIMIT_OFFSET: usize = 0x0000001C;
pub const RATE_LIMIT_RATE_LIMIT_SHIFT: u32 = 0;
pub const RATE_LIMIT_RATE_LIMIT_WIDTH: u32 = 8;
pub const RATE_LIMIT_RATE_LIMIT_MASK: u32 = 0x000000FF;
pub const SAFE_OUTPUT_OFFSET: usize = 0x00000020;
pub const SAFE_OUTPUT_SAFE_OUTPUT_SHIFT: u32 = 0;
pub const SAFE_OUTPUT_SAFE_OUTPUT_WIDTH: u32 = 16;
pub const SAFE_OUTPUT_SAFE_OUTPUT_MASK: u32 = 0x0000FFFF;
pub const FAULT_CTRL_OFFSET: usize = 0x00000024;
pub const FAULT_CTRL_FAULT_CLEAR_SHIFT: u32 = 0;
pub const FAULT_CTRL_FAULT_CLEAR_WIDTH: u32 = 1;
pub const FAULT_CTRL_FAULT_CLEAR_MASK: u32 = 0x00000001;
pub const STATUS_OFFSET: usize = 0x00000028;
pub const STATUS_MODE_SHIFT: u32 = 0;
pub const STATUS_MODE_WIDTH: u32 = 2;
pub const STATUS_MODE_MASK: u32 = 0x00000003;
pub const STATUS_FAULT_LATCHED_SHIFT: u32 = 2;
pub const STATUS_FAULT_LATCHED_WIDTH: u32 = 1;
pub const STATUS_FAULT_LATCHED_MASK: u32 = 0x00000004;
pub const STATUS_TIMEOUT_STATUS_SHIFT: u32 = 3;
pub const STATUS_TIMEOUT_STATUS_WIDTH: u32 = 1;
pub const STATUS_TIMEOUT_STATUS_MASK: u32 = 0x00000008;
pub const STATUS_STALE_STATUS_SHIFT: u32 = 4;
pub const STATUS_STALE_STATUS_WIDTH: u32 = 1;
pub const STATUS_STALE_STATUS_MASK: u32 = 0x00000010;
pub const STATUS_HEARTBEAT_SEEN_SHIFT: u32 = 5;
pub const STATUS_HEARTBEAT_SEEN_WIDTH: u32 = 1;
pub const STATUS_HEARTBEAT_SEEN_MASK: u32 = 0x00000020;
pub const LAST_CMD_OFFSET: usize = 0x0000002C;
pub const LAST_CMD_LAST_CMD_SHIFT: u32 = 0;
pub const LAST_CMD_LAST_CMD_WIDTH: u32 = 16;
pub const LAST_CMD_LAST_CMD_MASK: u32 = 0x0000FFFF;
pub const LAST_SEQ_OFFSET: usize = 0x00000030;
pub const LAST_SEQ_LAST_SEQ_SHIFT: u32 = 0;
pub const LAST_SEQ_LAST_SEQ_WIDTH: u32 = 16;
pub const LAST_SEQ_LAST_SEQ_MASK: u32 = 0x0000FFFF;
pub const TELEM_ACCEPTED_OFFSET: usize = 0x00000034;
pub const TELEM_ACCEPTED_ACCEPTED_PACKETS_SHIFT: u32 = 0;
pub const TELEM_ACCEPTED_ACCEPTED_PACKETS_WIDTH: u32 = 16;
pub const TELEM_ACCEPTED_ACCEPTED_PACKETS_MASK: u32 = 0x0000FFFF;
pub const TELEM_REJECTED_OFFSET: usize = 0x00000038;
pub const TELEM_REJECTED_REJECTED_PACKETS_SHIFT: u32 = 0;
pub const TELEM_REJECTED_REJECTED_PACKETS_WIDTH: u32 = 16;
pub const TELEM_REJECTED_REJECTED_PACKETS_MASK: u32 = 0x0000FFFF;
pub const TELEM_TIMEOUT_OFFSET: usize = 0x0000003C;
pub const TELEM_TIMEOUT_TIMEOUT_EVENTS_SHIFT: u32 = 0;
pub const TELEM_TIMEOUT_TIMEOUT_EVENTS_WIDTH: u32 = 16;
pub const TELEM_TIMEOUT_TIMEOUT_EVENTS_MASK: u32 = 0x0000FFFF;
pub const TELEM_STALE_OFFSET: usize = 0x00000040;
pub const TELEM_STALE_STALE_EVENTS_SHIFT: u32 = 0;
pub const TELEM_STALE_STALE_EVENTS_WIDTH: u32 = 16;
pub const TELEM_STALE_STALE_EVENTS_MASK: u32 = 0x0000FFFF;
pub const TELEM_FALLBACK_OFFSET: usize = 0x00000044;
pub const TELEM_FALLBACK_FALLBACK_ENTRIES_SHIFT: u32 = 0;
pub const TELEM_FALLBACK_FALLBACK_ENTRIES_WIDTH: u32 = 16;
pub const TELEM_FALLBACK_FALLBACK_ENTRIES_MASK: u32 = 0x0000FFFF;
pub const TELEM_LAST_VALID_SEQ_OFFSET: usize = 0x00000048;
pub const TELEM_LAST_VALID_SEQ_LAST_VALID_SEQ_SHIFT: u32 = 0;
pub const TELEM_LAST_VALID_SEQ_LAST_VALID_SEQ_WIDTH: u32 = 16;
pub const TELEM_LAST_VALID_SEQ_LAST_VALID_SEQ_MASK: u32 = 0x0000FFFF;

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
pub fn get_ctrl_mode_sel() -> u32 {
    (read_ctrl() & CTRL_MODE_SEL_MASK) >> CTRL_MODE_SEL_SHIFT
}

#[inline]
pub fn set_ctrl_mode_sel(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_MODE_SEL_MASK) | ((value << CTRL_MODE_SEL_SHIFT) & CTRL_MODE_SEL_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_reserved_error_en() -> u32 {
    (read_ctrl() & CTRL_RESERVED_ERROR_EN_MASK) >> CTRL_RESERVED_ERROR_EN_SHIFT
}

#[inline]
pub fn set_ctrl_reserved_error_en(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_RESERVED_ERROR_EN_MASK) | ((value << CTRL_RESERVED_ERROR_EN_SHIFT) & CTRL_RESERVED_ERROR_EN_MASK);
    write_ctrl(next);
}

#[inline]
pub fn read_reserved() -> u32 {
    read_reg(RESERVED_OFFSET)
}

#[inline]
pub fn write_reserved(value: u32) {
    write_reg(RESERVED_OFFSET, value)
}

#[inline]
pub fn get_reserved_reserved_error_flag() -> u32 {
    (read_reserved() & RESERVED_RESERVED_ERROR_FLAG_MASK) >> RESERVED_RESERVED_ERROR_FLAG_SHIFT
}

#[inline]
pub fn set_reserved_reserved_error_flag(value: u32) {
    let current = read_reserved();
    let next = (current & !RESERVED_RESERVED_ERROR_FLAG_MASK) | ((value << RESERVED_RESERVED_ERROR_FLAG_SHIFT) & RESERVED_RESERVED_ERROR_FLAG_MASK);
    write_reserved(next);
}

#[inline]
pub fn read_env_limit() -> u32 {
    read_reg(ENV_LIMIT_OFFSET)
}

#[inline]
pub fn write_env_limit(value: u32) {
    write_reg(ENV_LIMIT_OFFSET, value)
}

#[inline]
pub fn get_env_limit_env_limit() -> u32 {
    (read_env_limit() & ENV_LIMIT_ENV_LIMIT_MASK) >> ENV_LIMIT_ENV_LIMIT_SHIFT
}

#[inline]
pub fn set_env_limit_env_limit(value: u32) {
    let current = read_env_limit();
    let next = (current & !ENV_LIMIT_ENV_LIMIT_MASK) | ((value << ENV_LIMIT_ENV_LIMIT_SHIFT) & ENV_LIMIT_ENV_LIMIT_MASK);
    write_env_limit(next);
}

#[inline]
pub fn read_stale_timeout() -> u32 {
    read_reg(STALE_TIMEOUT_OFFSET)
}

#[inline]
pub fn write_stale_timeout(value: u32) {
    write_reg(STALE_TIMEOUT_OFFSET, value)
}

#[inline]
pub fn get_stale_timeout_stale_timeout() -> u32 {
    (read_stale_timeout() & STALE_TIMEOUT_STALE_TIMEOUT_MASK) >> STALE_TIMEOUT_STALE_TIMEOUT_SHIFT
}

#[inline]
pub fn set_stale_timeout_stale_timeout(value: u32) {
    let current = read_stale_timeout();
    let next = (current & !STALE_TIMEOUT_STALE_TIMEOUT_MASK) | ((value << STALE_TIMEOUT_STALE_TIMEOUT_SHIFT) & STALE_TIMEOUT_STALE_TIMEOUT_MASK);
    write_stale_timeout(next);
}

#[inline]
pub fn read_seq_base() -> u32 {
    read_reg(SEQ_BASE_OFFSET)
}

#[inline]
pub fn write_seq_base(value: u32) {
    write_reg(SEQ_BASE_OFFSET, value)
}

#[inline]
pub fn get_seq_base_seq_base() -> u32 {
    (read_seq_base() & SEQ_BASE_SEQ_BASE_MASK) >> SEQ_BASE_SEQ_BASE_SHIFT
}

#[inline]
pub fn set_seq_base_seq_base(value: u32) {
    let current = read_seq_base();
    let next = (current & !SEQ_BASE_SEQ_BASE_MASK) | ((value << SEQ_BASE_SEQ_BASE_SHIFT) & SEQ_BASE_SEQ_BASE_MASK);
    write_seq_base(next);
}

#[inline]
pub fn read_heartbeat_timeout() -> u32 {
    read_reg(HEARTBEAT_TIMEOUT_OFFSET)
}

#[inline]
pub fn write_heartbeat_timeout(value: u32) {
    write_reg(HEARTBEAT_TIMEOUT_OFFSET, value)
}

#[inline]
pub fn get_heartbeat_timeout_heartbeat_timeout() -> u32 {
    (read_heartbeat_timeout() & HEARTBEAT_TIMEOUT_HEARTBEAT_TIMEOUT_MASK) >> HEARTBEAT_TIMEOUT_HEARTBEAT_TIMEOUT_SHIFT
}

#[inline]
pub fn set_heartbeat_timeout_heartbeat_timeout(value: u32) {
    let current = read_heartbeat_timeout();
    let next = (current & !HEARTBEAT_TIMEOUT_HEARTBEAT_TIMEOUT_MASK) | ((value << HEARTBEAT_TIMEOUT_HEARTBEAT_TIMEOUT_SHIFT) & HEARTBEAT_TIMEOUT_HEARTBEAT_TIMEOUT_MASK);
    write_heartbeat_timeout(next);
}

#[inline]
pub fn read_act_clamp_min() -> u32 {
    read_reg(ACT_CLAMP_MIN_OFFSET)
}

#[inline]
pub fn write_act_clamp_min(value: u32) {
    write_reg(ACT_CLAMP_MIN_OFFSET, value)
}

#[inline]
pub fn get_act_clamp_min_act_min() -> u32 {
    (read_act_clamp_min() & ACT_CLAMP_MIN_ACT_MIN_MASK) >> ACT_CLAMP_MIN_ACT_MIN_SHIFT
}

#[inline]
pub fn set_act_clamp_min_act_min(value: u32) {
    let current = read_act_clamp_min();
    let next = (current & !ACT_CLAMP_MIN_ACT_MIN_MASK) | ((value << ACT_CLAMP_MIN_ACT_MIN_SHIFT) & ACT_CLAMP_MIN_ACT_MIN_MASK);
    write_act_clamp_min(next);
}

#[inline]
pub fn read_act_clamp_max() -> u32 {
    read_reg(ACT_CLAMP_MAX_OFFSET)
}

#[inline]
pub fn write_act_clamp_max(value: u32) {
    write_reg(ACT_CLAMP_MAX_OFFSET, value)
}

#[inline]
pub fn get_act_clamp_max_act_max() -> u32 {
    (read_act_clamp_max() & ACT_CLAMP_MAX_ACT_MAX_MASK) >> ACT_CLAMP_MAX_ACT_MAX_SHIFT
}

#[inline]
pub fn set_act_clamp_max_act_max(value: u32) {
    let current = read_act_clamp_max();
    let next = (current & !ACT_CLAMP_MAX_ACT_MAX_MASK) | ((value << ACT_CLAMP_MAX_ACT_MAX_SHIFT) & ACT_CLAMP_MAX_ACT_MAX_MASK);
    write_act_clamp_max(next);
}

#[inline]
pub fn read_rate_limit() -> u32 {
    read_reg(RATE_LIMIT_OFFSET)
}

#[inline]
pub fn write_rate_limit(value: u32) {
    write_reg(RATE_LIMIT_OFFSET, value)
}

#[inline]
pub fn get_rate_limit_rate_limit() -> u32 {
    (read_rate_limit() & RATE_LIMIT_RATE_LIMIT_MASK) >> RATE_LIMIT_RATE_LIMIT_SHIFT
}

#[inline]
pub fn set_rate_limit_rate_limit(value: u32) {
    let current = read_rate_limit();
    let next = (current & !RATE_LIMIT_RATE_LIMIT_MASK) | ((value << RATE_LIMIT_RATE_LIMIT_SHIFT) & RATE_LIMIT_RATE_LIMIT_MASK);
    write_rate_limit(next);
}

#[inline]
pub fn read_safe_output() -> u32 {
    read_reg(SAFE_OUTPUT_OFFSET)
}

#[inline]
pub fn write_safe_output(value: u32) {
    write_reg(SAFE_OUTPUT_OFFSET, value)
}

#[inline]
pub fn get_safe_output_safe_output() -> u32 {
    (read_safe_output() & SAFE_OUTPUT_SAFE_OUTPUT_MASK) >> SAFE_OUTPUT_SAFE_OUTPUT_SHIFT
}

#[inline]
pub fn set_safe_output_safe_output(value: u32) {
    let current = read_safe_output();
    let next = (current & !SAFE_OUTPUT_SAFE_OUTPUT_MASK) | ((value << SAFE_OUTPUT_SAFE_OUTPUT_SHIFT) & SAFE_OUTPUT_SAFE_OUTPUT_MASK);
    write_safe_output(next);
}

#[inline]
pub fn read_fault_ctrl() -> u32 {
    read_reg(FAULT_CTRL_OFFSET)
}

#[inline]
pub fn write_fault_ctrl(value: u32) {
    write_reg(FAULT_CTRL_OFFSET, value)
}

#[inline]
pub fn get_fault_ctrl_fault_clear() -> u32 {
    (read_fault_ctrl() & FAULT_CTRL_FAULT_CLEAR_MASK) >> FAULT_CTRL_FAULT_CLEAR_SHIFT
}

#[inline]
pub fn set_fault_ctrl_fault_clear(value: u32) {
    let current = read_fault_ctrl();
    let next = (current & !FAULT_CTRL_FAULT_CLEAR_MASK) | ((value << FAULT_CTRL_FAULT_CLEAR_SHIFT) & FAULT_CTRL_FAULT_CLEAR_MASK);
    write_fault_ctrl(next);
}

#[inline]
pub fn read_status() -> u32 {
    read_reg(STATUS_OFFSET)
}

#[inline]
pub fn get_status_mode() -> u32 {
    (read_status() & STATUS_MODE_MASK) >> STATUS_MODE_SHIFT
}

#[inline]
pub fn get_status_fault_latched() -> u32 {
    (read_status() & STATUS_FAULT_LATCHED_MASK) >> STATUS_FAULT_LATCHED_SHIFT
}

#[inline]
pub fn get_status_timeout_status() -> u32 {
    (read_status() & STATUS_TIMEOUT_STATUS_MASK) >> STATUS_TIMEOUT_STATUS_SHIFT
}

#[inline]
pub fn get_status_stale_status() -> u32 {
    (read_status() & STATUS_STALE_STATUS_MASK) >> STATUS_STALE_STATUS_SHIFT
}

#[inline]
pub fn get_status_heartbeat_seen() -> u32 {
    (read_status() & STATUS_HEARTBEAT_SEEN_MASK) >> STATUS_HEARTBEAT_SEEN_SHIFT
}

#[inline]
pub fn read_last_cmd() -> u32 {
    read_reg(LAST_CMD_OFFSET)
}

#[inline]
pub fn get_last_cmd_last_cmd() -> u32 {
    (read_last_cmd() & LAST_CMD_LAST_CMD_MASK) >> LAST_CMD_LAST_CMD_SHIFT
}

#[inline]
pub fn read_last_seq() -> u32 {
    read_reg(LAST_SEQ_OFFSET)
}

#[inline]
pub fn get_last_seq_last_seq() -> u32 {
    (read_last_seq() & LAST_SEQ_LAST_SEQ_MASK) >> LAST_SEQ_LAST_SEQ_SHIFT
}

#[inline]
pub fn read_telem_accepted() -> u32 {
    read_reg(TELEM_ACCEPTED_OFFSET)
}

#[inline]
pub fn get_telem_accepted_accepted_packets() -> u32 {
    (read_telem_accepted() & TELEM_ACCEPTED_ACCEPTED_PACKETS_MASK) >> TELEM_ACCEPTED_ACCEPTED_PACKETS_SHIFT
}

#[inline]
pub fn read_telem_rejected() -> u32 {
    read_reg(TELEM_REJECTED_OFFSET)
}

#[inline]
pub fn get_telem_rejected_rejected_packets() -> u32 {
    (read_telem_rejected() & TELEM_REJECTED_REJECTED_PACKETS_MASK) >> TELEM_REJECTED_REJECTED_PACKETS_SHIFT
}

#[inline]
pub fn read_telem_timeout() -> u32 {
    read_reg(TELEM_TIMEOUT_OFFSET)
}

#[inline]
pub fn get_telem_timeout_timeout_events() -> u32 {
    (read_telem_timeout() & TELEM_TIMEOUT_TIMEOUT_EVENTS_MASK) >> TELEM_TIMEOUT_TIMEOUT_EVENTS_SHIFT
}

#[inline]
pub fn read_telem_stale() -> u32 {
    read_reg(TELEM_STALE_OFFSET)
}

#[inline]
pub fn get_telem_stale_stale_events() -> u32 {
    (read_telem_stale() & TELEM_STALE_STALE_EVENTS_MASK) >> TELEM_STALE_STALE_EVENTS_SHIFT
}

#[inline]
pub fn read_telem_fallback() -> u32 {
    read_reg(TELEM_FALLBACK_OFFSET)
}

#[inline]
pub fn get_telem_fallback_fallback_entries() -> u32 {
    (read_telem_fallback() & TELEM_FALLBACK_FALLBACK_ENTRIES_MASK) >> TELEM_FALLBACK_FALLBACK_ENTRIES_SHIFT
}

#[inline]
pub fn read_telem_last_valid_seq() -> u32 {
    read_reg(TELEM_LAST_VALID_SEQ_OFFSET)
}

#[inline]
pub fn get_telem_last_valid_seq_last_valid_seq() -> u32 {
    (read_telem_last_valid_seq() & TELEM_LAST_VALID_SEQ_LAST_VALID_SEQ_MASK) >> TELEM_LAST_VALID_SEQ_LAST_VALID_SEQ_SHIFT
}

