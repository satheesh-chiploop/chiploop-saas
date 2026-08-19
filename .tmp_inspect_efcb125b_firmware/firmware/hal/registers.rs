use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const CTRL_OFFSET: usize = 0x00000000;
pub const CTRL_MODE_SHIFT: u32 = 0;
pub const CTRL_MODE_WIDTH: u32 = 2;
pub const CTRL_MODE_MASK: u32 = 0x00000003;
pub const CTRL_CMD_VALID_SHIFT: u32 = 2;
pub const CTRL_CMD_VALID_WIDTH: u32 = 1;
pub const CTRL_CMD_VALID_MASK: u32 = 0x00000004;
pub const CTRL_HOLD_LAST_SAFE_SHIFT: u32 = 3;
pub const CTRL_HOLD_LAST_SAFE_WIDTH: u32 = 1;
pub const CTRL_HOLD_LAST_SAFE_MASK: u32 = 0x00000008;
pub const CTRL_FAULT_CLEAR_SHIFT: u32 = 4;
pub const CTRL_FAULT_CLEAR_WIDTH: u32 = 1;
pub const CTRL_FAULT_CLEAR_MASK: u32 = 0x00000010;
pub const CTRL_IRQ_ACK_SHIFT: u32 = 5;
pub const CTRL_IRQ_ACK_WIDTH: u32 = 1;
pub const CTRL_IRQ_ACK_MASK: u32 = 0x00000020;
pub const CTRL_IRQ_ENABLE_SHIFT: u32 = 8;
pub const CTRL_IRQ_ENABLE_WIDTH: u32 = 8;
pub const CTRL_IRQ_ENABLE_MASK: u32 = 0x0000FF00;
pub const VELOCITY_Q8_8_OFFSET: usize = 0x00000004;
pub const VELOCITY_Q8_8_VELOCITY_Q8_8_SHIFT: u32 = 0;
pub const VELOCITY_Q8_8_VELOCITY_Q8_8_WIDTH: u32 = 16;
pub const VELOCITY_Q8_8_VELOCITY_Q8_8_MASK: u32 = 0x0000FFFF;
pub const GEOMETRY_HANDLE_OFFSET: usize = 0x00000008;
pub const GEOMETRY_HANDLE_GEOMETRY_HANDLE_SHIFT: u32 = 0;
pub const GEOMETRY_HANDLE_GEOMETRY_HANDLE_WIDTH: u32 = 16;
pub const GEOMETRY_HANDLE_GEOMETRY_HANDLE_MASK: u32 = 0x0000FFFF;
pub const SEQ_CTRL_OFFSET: usize = 0x0000000C;
pub const SEQ_CTRL_REQUEST_SEQ_SHIFT: u32 = 0;
pub const SEQ_CTRL_REQUEST_SEQ_WIDTH: u32 = 16;
pub const SEQ_CTRL_REQUEST_SEQ_MASK: u32 = 0x0000FFFF;
pub const SEQ_CTRL_LAST_ACCEPTED_SEQ_RO_SHIFT: u32 = 16;
pub const SEQ_CTRL_LAST_ACCEPTED_SEQ_RO_WIDTH: u32 = 16;
pub const SEQ_CTRL_LAST_ACCEPTED_SEQ_RO_MASK: u32 = 0xFFFF0000;
pub const TIMEOUT_AND_ENVELOPE_OFFSET: usize = 0x00000010;
pub const TIMEOUT_AND_ENVELOPE_TIMEOUT_THRESHOLD_SHIFT: u32 = 0;
pub const TIMEOUT_AND_ENVELOPE_TIMEOUT_THRESHOLD_WIDTH: u32 = 16;
pub const TIMEOUT_AND_ENVELOPE_TIMEOUT_THRESHOLD_MASK: u32 = 0x0000FFFF;
pub const TIMEOUT_AND_ENVELOPE_VELOCITY_LOW_LIMIT_SHIFT: u32 = 16;
pub const TIMEOUT_AND_ENVELOPE_VELOCITY_LOW_LIMIT_WIDTH: u32 = 8;
pub const TIMEOUT_AND_ENVELOPE_VELOCITY_LOW_LIMIT_MASK: u32 = 0x00FF0000;
pub const TIMEOUT_AND_ENVELOPE_VELOCITY_HIGH_LIMIT_SHIFT: u32 = 24;
pub const TIMEOUT_AND_ENVELOPE_VELOCITY_HIGH_LIMIT_WIDTH: u32 = 8;
pub const TIMEOUT_AND_ENVELOPE_VELOCITY_HIGH_LIMIT_MASK: u32 = 0xFF000000;
pub const ACTUATOR_LIMITS_OFFSET: usize = 0x00000014;
pub const ACTUATOR_LIMITS_ACTUATOR_MIN_SHIFT: u32 = 0;
pub const ACTUATOR_LIMITS_ACTUATOR_MIN_WIDTH: u32 = 16;
pub const ACTUATOR_LIMITS_ACTUATOR_MIN_MASK: u32 = 0x0000FFFF;
pub const ACTUATOR_LIMITS_ACTUATOR_MAX_SHIFT: u32 = 16;
pub const ACTUATOR_LIMITS_ACTUATOR_MAX_WIDTH: u32 = 16;
pub const ACTUATOR_LIMITS_ACTUATOR_MAX_MASK: u32 = 0xFFFF0000;
pub const ACTUATOR_SLEW_OFFSET: usize = 0x00000018;
pub const ACTUATOR_SLEW_ACTUATOR_SLEW_SHIFT: u32 = 0;
pub const ACTUATOR_SLEW_ACTUATOR_SLEW_WIDTH: u32 = 16;
pub const ACTUATOR_SLEW_ACTUATOR_SLEW_MASK: u32 = 0x0000FFFF;
pub const SAFE_STATE_OFFSET: usize = 0x0000001C;
pub const SAFE_STATE_SAFE_STATE_CMD_SHIFT: u32 = 0;
pub const SAFE_STATE_SAFE_STATE_CMD_WIDTH: u32 = 16;
pub const SAFE_STATE_SAFE_STATE_CMD_MASK: u32 = 0x0000FFFF;
pub const STATUS0_OFFSET: usize = 0x00000020;
pub const STATUS0_OUTSTANDING_REQ_SHIFT: u32 = 0;
pub const STATUS0_OUTSTANDING_REQ_WIDTH: u32 = 1;
pub const STATUS0_OUTSTANDING_REQ_MASK: u32 = 0x00000001;
pub const STATUS0_STATUS_SAFE_STATE_SHIFT: u32 = 1;
pub const STATUS0_STATUS_SAFE_STATE_WIDTH: u32 = 1;
pub const STATUS0_STATUS_SAFE_STATE_MASK: u32 = 0x00000002;
pub const STATUS0_STATUS_FAULT_LATCHED_SHIFT: u32 = 2;
pub const STATUS0_STATUS_FAULT_LATCHED_WIDTH: u32 = 1;
pub const STATUS0_STATUS_FAULT_LATCHED_MASK: u32 = 0x00000004;
pub const STATUS0_STATUS_ACTUATOR_VALID_SHIFT: u32 = 3;
pub const STATUS0_STATUS_ACTUATOR_VALID_WIDTH: u32 = 1;
pub const STATUS0_STATUS_ACTUATOR_VALID_MASK: u32 = 0x00000008;
pub const STATUS0_STATUS_FAULT_CODE_SHIFT: u32 = 8;
pub const STATUS0_STATUS_FAULT_CODE_WIDTH: u32 = 8;
pub const STATUS0_STATUS_FAULT_CODE_MASK: u32 = 0x0000FF00;
pub const STATUS1_OFFSET: usize = 0x00000024;
pub const STATUS1_STATUS_TIMEOUT_COUNT_SHIFT: u32 = 0;
pub const STATUS1_STATUS_TIMEOUT_COUNT_WIDTH: u32 = 16;
pub const STATUS1_STATUS_TIMEOUT_COUNT_MASK: u32 = 0x0000FFFF;
pub const STATUS1_STATUS_STALE_REJECT_COUNT_SHIFT: u32 = 16;
pub const STATUS1_STATUS_STALE_REJECT_COUNT_WIDTH: u32 = 16;
pub const STATUS1_STATUS_STALE_REJECT_COUNT_MASK: u32 = 0xFFFF0000;
pub const STATUS2_OFFSET: usize = 0x00000028;
pub const STATUS2_STATUS_INVALID_ENV_COUNT_SHIFT: u32 = 0;
pub const STATUS2_STATUS_INVALID_ENV_COUNT_WIDTH: u32 = 16;
pub const STATUS2_STATUS_INVALID_ENV_COUNT_MASK: u32 = 0x0000FFFF;
pub const STATUS2_STATUS_AGE_COUNTER_SHIFT: u32 = 16;
pub const STATUS2_STATUS_AGE_COUNTER_WIDTH: u32 = 16;
pub const STATUS2_STATUS_AGE_COUNTER_MASK: u32 = 0xFFFF0000;
pub const STATUS3_OFFSET: usize = 0x0000002C;
pub const STATUS3_STATUS_LAST_ACCEPTED_SEQ_SHIFT: u32 = 0;
pub const STATUS3_STATUS_LAST_ACCEPTED_SEQ_WIDTH: u32 = 16;
pub const STATUS3_STATUS_LAST_ACCEPTED_SEQ_MASK: u32 = 0x0000FFFF;
pub const STATUS3_STATUS_RESPONSE_SEQ_SHIFT: u32 = 16;
pub const STATUS3_STATUS_RESPONSE_SEQ_WIDTH: u32 = 16;
pub const STATUS3_STATUS_RESPONSE_SEQ_MASK: u32 = 0xFFFF0000;
pub const STATUS4_OFFSET: usize = 0x00000030;
pub const STATUS4_STATUS_LAST_REQ_WORD_LO_SHIFT: u32 = 0;
pub const STATUS4_STATUS_LAST_REQ_WORD_LO_WIDTH: u32 = 32;
pub const STATUS4_STATUS_LAST_REQ_WORD_LO_MASK: u32 = 0xFFFFFFFF;
pub const STATUS5_OFFSET: usize = 0x00000034;
pub const STATUS5_STATUS_LAST_REQ_WORD_HI_SHIFT: u32 = 0;
pub const STATUS5_STATUS_LAST_REQ_WORD_HI_WIDTH: u32 = 32;
pub const STATUS5_STATUS_LAST_REQ_WORD_HI_MASK: u32 = 0xFFFFFFFF;
pub const STATUS6_OFFSET: usize = 0x00000038;
pub const STATUS6_STATUS_LAST_RESP_WORD_LO_SHIFT: u32 = 0;
pub const STATUS6_STATUS_LAST_RESP_WORD_LO_WIDTH: u32 = 32;
pub const STATUS6_STATUS_LAST_RESP_WORD_LO_MASK: u32 = 0xFFFFFFFF;
pub const STATUS7_OFFSET: usize = 0x0000003C;
pub const STATUS7_STATUS_LAST_RESP_WORD_HI_SHIFT: u32 = 0;
pub const STATUS7_STATUS_LAST_RESP_WORD_HI_WIDTH: u32 = 32;
pub const STATUS7_STATUS_LAST_RESP_WORD_HI_MASK: u32 = 0xFFFFFFFF;
pub const IRQ_STATUS_OFFSET: usize = 0x00000040;
pub const IRQ_STATUS_RESP_READY_STICKY_SHIFT: u32 = 0;
pub const IRQ_STATUS_RESP_READY_STICKY_WIDTH: u32 = 1;
pub const IRQ_STATUS_RESP_READY_STICKY_MASK: u32 = 0x00000001;
pub const IRQ_STATUS_TIMEOUT_STICKY_SHIFT: u32 = 1;
pub const IRQ_STATUS_TIMEOUT_STICKY_WIDTH: u32 = 1;
pub const IRQ_STATUS_TIMEOUT_STICKY_MASK: u32 = 0x00000002;
pub const IRQ_STATUS_STALE_REJECT_STICKY_SHIFT: u32 = 2;
pub const IRQ_STATUS_STALE_REJECT_STICKY_WIDTH: u32 = 1;
pub const IRQ_STATUS_STALE_REJECT_STICKY_MASK: u32 = 0x00000004;
pub const IRQ_STATUS_INVALID_ENV_STICKY_SHIFT: u32 = 3;
pub const IRQ_STATUS_INVALID_ENV_STICKY_WIDTH: u32 = 1;
pub const IRQ_STATUS_INVALID_ENV_STICKY_MASK: u32 = 0x00000008;
pub const IRQ_STATUS_FAULT_CLEAR_EVENT_SHIFT: u32 = 4;
pub const IRQ_STATUS_FAULT_CLEAR_EVENT_WIDTH: u32 = 1;
pub const IRQ_STATUS_FAULT_CLEAR_EVENT_MASK: u32 = 0x00000010;
pub const FAULT_STATUS_OFFSET: usize = 0x00000044;
pub const FAULT_STATUS_FAULT_CODE_SHIFT: u32 = 0;
pub const FAULT_STATUS_FAULT_CODE_WIDTH: u32 = 8;
pub const FAULT_STATUS_FAULT_CODE_MASK: u32 = 0x000000FF;
pub const FAULT_STATUS_FAULT_LATCHED_SHIFT: u32 = 8;
pub const FAULT_STATUS_FAULT_LATCHED_WIDTH: u32 = 1;
pub const FAULT_STATUS_FAULT_LATCHED_MASK: u32 = 0x00000100;
pub const FAULT_STATUS_SAFE_STATE_SHIFT: u32 = 9;
pub const FAULT_STATUS_SAFE_STATE_WIDTH: u32 = 1;
pub const FAULT_STATUS_SAFE_STATE_MASK: u32 = 0x00000200;

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
pub fn get_ctrl_cmd_valid() -> u32 {
    (read_ctrl() & CTRL_CMD_VALID_MASK) >> CTRL_CMD_VALID_SHIFT
}

#[inline]
pub fn set_ctrl_cmd_valid(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_CMD_VALID_MASK) | ((value << CTRL_CMD_VALID_SHIFT) & CTRL_CMD_VALID_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_hold_last_safe() -> u32 {
    (read_ctrl() & CTRL_HOLD_LAST_SAFE_MASK) >> CTRL_HOLD_LAST_SAFE_SHIFT
}

#[inline]
pub fn set_ctrl_hold_last_safe(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_HOLD_LAST_SAFE_MASK) | ((value << CTRL_HOLD_LAST_SAFE_SHIFT) & CTRL_HOLD_LAST_SAFE_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_fault_clear() -> u32 {
    (read_ctrl() & CTRL_FAULT_CLEAR_MASK) >> CTRL_FAULT_CLEAR_SHIFT
}

#[inline]
pub fn set_ctrl_fault_clear(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_FAULT_CLEAR_MASK) | ((value << CTRL_FAULT_CLEAR_SHIFT) & CTRL_FAULT_CLEAR_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_irq_ack() -> u32 {
    (read_ctrl() & CTRL_IRQ_ACK_MASK) >> CTRL_IRQ_ACK_SHIFT
}

#[inline]
pub fn set_ctrl_irq_ack(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_IRQ_ACK_MASK) | ((value << CTRL_IRQ_ACK_SHIFT) & CTRL_IRQ_ACK_MASK);
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
pub fn read_velocity_q8_8() -> u32 {
    read_reg(VELOCITY_Q8_8_OFFSET)
}

#[inline]
pub fn write_velocity_q8_8(value: u32) {
    write_reg(VELOCITY_Q8_8_OFFSET, value)
}

#[inline]
pub fn get_velocity_q8_8_velocity_q8_8() -> u32 {
    (read_velocity_q8_8() & VELOCITY_Q8_8_VELOCITY_Q8_8_MASK) >> VELOCITY_Q8_8_VELOCITY_Q8_8_SHIFT
}

#[inline]
pub fn set_velocity_q8_8_velocity_q8_8(value: u32) {
    let current = read_velocity_q8_8();
    let next = (current & !VELOCITY_Q8_8_VELOCITY_Q8_8_MASK) | ((value << VELOCITY_Q8_8_VELOCITY_Q8_8_SHIFT) & VELOCITY_Q8_8_VELOCITY_Q8_8_MASK);
    write_velocity_q8_8(next);
}

#[inline]
pub fn read_geometry_handle() -> u32 {
    read_reg(GEOMETRY_HANDLE_OFFSET)
}

#[inline]
pub fn write_geometry_handle(value: u32) {
    write_reg(GEOMETRY_HANDLE_OFFSET, value)
}

#[inline]
pub fn get_geometry_handle_geometry_handle() -> u32 {
    (read_geometry_handle() & GEOMETRY_HANDLE_GEOMETRY_HANDLE_MASK) >> GEOMETRY_HANDLE_GEOMETRY_HANDLE_SHIFT
}

#[inline]
pub fn set_geometry_handle_geometry_handle(value: u32) {
    let current = read_geometry_handle();
    let next = (current & !GEOMETRY_HANDLE_GEOMETRY_HANDLE_MASK) | ((value << GEOMETRY_HANDLE_GEOMETRY_HANDLE_SHIFT) & GEOMETRY_HANDLE_GEOMETRY_HANDLE_MASK);
    write_geometry_handle(next);
}

#[inline]
pub fn read_seq_ctrl() -> u32 {
    read_reg(SEQ_CTRL_OFFSET)
}

#[inline]
pub fn write_seq_ctrl(value: u32) {
    write_reg(SEQ_CTRL_OFFSET, value)
}

#[inline]
pub fn get_seq_ctrl_request_seq() -> u32 {
    (read_seq_ctrl() & SEQ_CTRL_REQUEST_SEQ_MASK) >> SEQ_CTRL_REQUEST_SEQ_SHIFT
}

#[inline]
pub fn set_seq_ctrl_request_seq(value: u32) {
    let current = read_seq_ctrl();
    let next = (current & !SEQ_CTRL_REQUEST_SEQ_MASK) | ((value << SEQ_CTRL_REQUEST_SEQ_SHIFT) & SEQ_CTRL_REQUEST_SEQ_MASK);
    write_seq_ctrl(next);
}

#[inline]
pub fn get_seq_ctrl_last_accepted_seq_ro() -> u32 {
    (read_seq_ctrl() & SEQ_CTRL_LAST_ACCEPTED_SEQ_RO_MASK) >> SEQ_CTRL_LAST_ACCEPTED_SEQ_RO_SHIFT
}

#[inline]
pub fn read_timeout_and_envelope() -> u32 {
    read_reg(TIMEOUT_AND_ENVELOPE_OFFSET)
}

#[inline]
pub fn write_timeout_and_envelope(value: u32) {
    write_reg(TIMEOUT_AND_ENVELOPE_OFFSET, value)
}

#[inline]
pub fn get_timeout_and_envelope_timeout_threshold() -> u32 {
    (read_timeout_and_envelope() & TIMEOUT_AND_ENVELOPE_TIMEOUT_THRESHOLD_MASK) >> TIMEOUT_AND_ENVELOPE_TIMEOUT_THRESHOLD_SHIFT
}

#[inline]
pub fn set_timeout_and_envelope_timeout_threshold(value: u32) {
    let current = read_timeout_and_envelope();
    let next = (current & !TIMEOUT_AND_ENVELOPE_TIMEOUT_THRESHOLD_MASK) | ((value << TIMEOUT_AND_ENVELOPE_TIMEOUT_THRESHOLD_SHIFT) & TIMEOUT_AND_ENVELOPE_TIMEOUT_THRESHOLD_MASK);
    write_timeout_and_envelope(next);
}

#[inline]
pub fn get_timeout_and_envelope_velocity_low_limit() -> u32 {
    (read_timeout_and_envelope() & TIMEOUT_AND_ENVELOPE_VELOCITY_LOW_LIMIT_MASK) >> TIMEOUT_AND_ENVELOPE_VELOCITY_LOW_LIMIT_SHIFT
}

#[inline]
pub fn set_timeout_and_envelope_velocity_low_limit(value: u32) {
    let current = read_timeout_and_envelope();
    let next = (current & !TIMEOUT_AND_ENVELOPE_VELOCITY_LOW_LIMIT_MASK) | ((value << TIMEOUT_AND_ENVELOPE_VELOCITY_LOW_LIMIT_SHIFT) & TIMEOUT_AND_ENVELOPE_VELOCITY_LOW_LIMIT_MASK);
    write_timeout_and_envelope(next);
}

#[inline]
pub fn get_timeout_and_envelope_velocity_high_limit() -> u32 {
    (read_timeout_and_envelope() & TIMEOUT_AND_ENVELOPE_VELOCITY_HIGH_LIMIT_MASK) >> TIMEOUT_AND_ENVELOPE_VELOCITY_HIGH_LIMIT_SHIFT
}

#[inline]
pub fn set_timeout_and_envelope_velocity_high_limit(value: u32) {
    let current = read_timeout_and_envelope();
    let next = (current & !TIMEOUT_AND_ENVELOPE_VELOCITY_HIGH_LIMIT_MASK) | ((value << TIMEOUT_AND_ENVELOPE_VELOCITY_HIGH_LIMIT_SHIFT) & TIMEOUT_AND_ENVELOPE_VELOCITY_HIGH_LIMIT_MASK);
    write_timeout_and_envelope(next);
}

#[inline]
pub fn read_actuator_limits() -> u32 {
    read_reg(ACTUATOR_LIMITS_OFFSET)
}

#[inline]
pub fn write_actuator_limits(value: u32) {
    write_reg(ACTUATOR_LIMITS_OFFSET, value)
}

#[inline]
pub fn get_actuator_limits_actuator_min() -> u32 {
    (read_actuator_limits() & ACTUATOR_LIMITS_ACTUATOR_MIN_MASK) >> ACTUATOR_LIMITS_ACTUATOR_MIN_SHIFT
}

#[inline]
pub fn set_actuator_limits_actuator_min(value: u32) {
    let current = read_actuator_limits();
    let next = (current & !ACTUATOR_LIMITS_ACTUATOR_MIN_MASK) | ((value << ACTUATOR_LIMITS_ACTUATOR_MIN_SHIFT) & ACTUATOR_LIMITS_ACTUATOR_MIN_MASK);
    write_actuator_limits(next);
}

#[inline]
pub fn get_actuator_limits_actuator_max() -> u32 {
    (read_actuator_limits() & ACTUATOR_LIMITS_ACTUATOR_MAX_MASK) >> ACTUATOR_LIMITS_ACTUATOR_MAX_SHIFT
}

#[inline]
pub fn set_actuator_limits_actuator_max(value: u32) {
    let current = read_actuator_limits();
    let next = (current & !ACTUATOR_LIMITS_ACTUATOR_MAX_MASK) | ((value << ACTUATOR_LIMITS_ACTUATOR_MAX_SHIFT) & ACTUATOR_LIMITS_ACTUATOR_MAX_MASK);
    write_actuator_limits(next);
}

#[inline]
pub fn read_actuator_slew() -> u32 {
    read_reg(ACTUATOR_SLEW_OFFSET)
}

#[inline]
pub fn write_actuator_slew(value: u32) {
    write_reg(ACTUATOR_SLEW_OFFSET, value)
}

#[inline]
pub fn get_actuator_slew_actuator_slew() -> u32 {
    (read_actuator_slew() & ACTUATOR_SLEW_ACTUATOR_SLEW_MASK) >> ACTUATOR_SLEW_ACTUATOR_SLEW_SHIFT
}

#[inline]
pub fn set_actuator_slew_actuator_slew(value: u32) {
    let current = read_actuator_slew();
    let next = (current & !ACTUATOR_SLEW_ACTUATOR_SLEW_MASK) | ((value << ACTUATOR_SLEW_ACTUATOR_SLEW_SHIFT) & ACTUATOR_SLEW_ACTUATOR_SLEW_MASK);
    write_actuator_slew(next);
}

#[inline]
pub fn read_safe_state() -> u32 {
    read_reg(SAFE_STATE_OFFSET)
}

#[inline]
pub fn write_safe_state(value: u32) {
    write_reg(SAFE_STATE_OFFSET, value)
}

#[inline]
pub fn get_safe_state_safe_state_cmd() -> u32 {
    (read_safe_state() & SAFE_STATE_SAFE_STATE_CMD_MASK) >> SAFE_STATE_SAFE_STATE_CMD_SHIFT
}

#[inline]
pub fn set_safe_state_safe_state_cmd(value: u32) {
    let current = read_safe_state();
    let next = (current & !SAFE_STATE_SAFE_STATE_CMD_MASK) | ((value << SAFE_STATE_SAFE_STATE_CMD_SHIFT) & SAFE_STATE_SAFE_STATE_CMD_MASK);
    write_safe_state(next);
}

#[inline]
pub fn read_status0() -> u32 {
    read_reg(STATUS0_OFFSET)
}

#[inline]
pub fn get_status0_outstanding_req() -> u32 {
    (read_status0() & STATUS0_OUTSTANDING_REQ_MASK) >> STATUS0_OUTSTANDING_REQ_SHIFT
}

#[inline]
pub fn get_status0_status_safe_state() -> u32 {
    (read_status0() & STATUS0_STATUS_SAFE_STATE_MASK) >> STATUS0_STATUS_SAFE_STATE_SHIFT
}

#[inline]
pub fn get_status0_status_fault_latched() -> u32 {
    (read_status0() & STATUS0_STATUS_FAULT_LATCHED_MASK) >> STATUS0_STATUS_FAULT_LATCHED_SHIFT
}

#[inline]
pub fn get_status0_status_actuator_valid() -> u32 {
    (read_status0() & STATUS0_STATUS_ACTUATOR_VALID_MASK) >> STATUS0_STATUS_ACTUATOR_VALID_SHIFT
}

#[inline]
pub fn get_status0_status_fault_code() -> u32 {
    (read_status0() & STATUS0_STATUS_FAULT_CODE_MASK) >> STATUS0_STATUS_FAULT_CODE_SHIFT
}

#[inline]
pub fn read_status1() -> u32 {
    read_reg(STATUS1_OFFSET)
}

#[inline]
pub fn get_status1_status_timeout_count() -> u32 {
    (read_status1() & STATUS1_STATUS_TIMEOUT_COUNT_MASK) >> STATUS1_STATUS_TIMEOUT_COUNT_SHIFT
}

#[inline]
pub fn get_status1_status_stale_reject_count() -> u32 {
    (read_status1() & STATUS1_STATUS_STALE_REJECT_COUNT_MASK) >> STATUS1_STATUS_STALE_REJECT_COUNT_SHIFT
}

#[inline]
pub fn read_status2() -> u32 {
    read_reg(STATUS2_OFFSET)
}

#[inline]
pub fn get_status2_status_invalid_env_count() -> u32 {
    (read_status2() & STATUS2_STATUS_INVALID_ENV_COUNT_MASK) >> STATUS2_STATUS_INVALID_ENV_COUNT_SHIFT
}

#[inline]
pub fn get_status2_status_age_counter() -> u32 {
    (read_status2() & STATUS2_STATUS_AGE_COUNTER_MASK) >> STATUS2_STATUS_AGE_COUNTER_SHIFT
}

#[inline]
pub fn read_status3() -> u32 {
    read_reg(STATUS3_OFFSET)
}

#[inline]
pub fn get_status3_status_last_accepted_seq() -> u32 {
    (read_status3() & STATUS3_STATUS_LAST_ACCEPTED_SEQ_MASK) >> STATUS3_STATUS_LAST_ACCEPTED_SEQ_SHIFT
}

#[inline]
pub fn get_status3_status_response_seq() -> u32 {
    (read_status3() & STATUS3_STATUS_RESPONSE_SEQ_MASK) >> STATUS3_STATUS_RESPONSE_SEQ_SHIFT
}

#[inline]
pub fn read_status4() -> u32 {
    read_reg(STATUS4_OFFSET)
}

#[inline]
pub fn get_status4_status_last_req_word_lo() -> u32 {
    (read_status4() & STATUS4_STATUS_LAST_REQ_WORD_LO_MASK) >> STATUS4_STATUS_LAST_REQ_WORD_LO_SHIFT
}

#[inline]
pub fn read_status5() -> u32 {
    read_reg(STATUS5_OFFSET)
}

#[inline]
pub fn get_status5_status_last_req_word_hi() -> u32 {
    (read_status5() & STATUS5_STATUS_LAST_REQ_WORD_HI_MASK) >> STATUS5_STATUS_LAST_REQ_WORD_HI_SHIFT
}

#[inline]
pub fn read_status6() -> u32 {
    read_reg(STATUS6_OFFSET)
}

#[inline]
pub fn get_status6_status_last_resp_word_lo() -> u32 {
    (read_status6() & STATUS6_STATUS_LAST_RESP_WORD_LO_MASK) >> STATUS6_STATUS_LAST_RESP_WORD_LO_SHIFT
}

#[inline]
pub fn read_status7() -> u32 {
    read_reg(STATUS7_OFFSET)
}

#[inline]
pub fn get_status7_status_last_resp_word_hi() -> u32 {
    (read_status7() & STATUS7_STATUS_LAST_RESP_WORD_HI_MASK) >> STATUS7_STATUS_LAST_RESP_WORD_HI_SHIFT
}

#[inline]
pub fn read_irq_status() -> u32 {
    read_reg(IRQ_STATUS_OFFSET)
}

#[inline]
pub fn write_irq_status(value: u32) {
    write_reg(IRQ_STATUS_OFFSET, value)
}

#[inline]
pub fn get_irq_status_resp_ready_sticky() -> u32 {
    (read_irq_status() & IRQ_STATUS_RESP_READY_STICKY_MASK) >> IRQ_STATUS_RESP_READY_STICKY_SHIFT
}

#[inline]
pub fn set_irq_status_resp_ready_sticky(value: u32) {
    let current = read_irq_status();
    let next = (current & !IRQ_STATUS_RESP_READY_STICKY_MASK) | ((value << IRQ_STATUS_RESP_READY_STICKY_SHIFT) & IRQ_STATUS_RESP_READY_STICKY_MASK);
    write_irq_status(next);
}

#[inline]
pub fn get_irq_status_timeout_sticky() -> u32 {
    (read_irq_status() & IRQ_STATUS_TIMEOUT_STICKY_MASK) >> IRQ_STATUS_TIMEOUT_STICKY_SHIFT
}

#[inline]
pub fn set_irq_status_timeout_sticky(value: u32) {
    let current = read_irq_status();
    let next = (current & !IRQ_STATUS_TIMEOUT_STICKY_MASK) | ((value << IRQ_STATUS_TIMEOUT_STICKY_SHIFT) & IRQ_STATUS_TIMEOUT_STICKY_MASK);
    write_irq_status(next);
}

#[inline]
pub fn get_irq_status_stale_reject_sticky() -> u32 {
    (read_irq_status() & IRQ_STATUS_STALE_REJECT_STICKY_MASK) >> IRQ_STATUS_STALE_REJECT_STICKY_SHIFT
}

#[inline]
pub fn set_irq_status_stale_reject_sticky(value: u32) {
    let current = read_irq_status();
    let next = (current & !IRQ_STATUS_STALE_REJECT_STICKY_MASK) | ((value << IRQ_STATUS_STALE_REJECT_STICKY_SHIFT) & IRQ_STATUS_STALE_REJECT_STICKY_MASK);
    write_irq_status(next);
}

#[inline]
pub fn get_irq_status_invalid_env_sticky() -> u32 {
    (read_irq_status() & IRQ_STATUS_INVALID_ENV_STICKY_MASK) >> IRQ_STATUS_INVALID_ENV_STICKY_SHIFT
}

#[inline]
pub fn set_irq_status_invalid_env_sticky(value: u32) {
    let current = read_irq_status();
    let next = (current & !IRQ_STATUS_INVALID_ENV_STICKY_MASK) | ((value << IRQ_STATUS_INVALID_ENV_STICKY_SHIFT) & IRQ_STATUS_INVALID_ENV_STICKY_MASK);
    write_irq_status(next);
}

#[inline]
pub fn get_irq_status_fault_clear_event() -> u32 {
    (read_irq_status() & IRQ_STATUS_FAULT_CLEAR_EVENT_MASK) >> IRQ_STATUS_FAULT_CLEAR_EVENT_SHIFT
}

#[inline]
pub fn set_irq_status_fault_clear_event(value: u32) {
    let current = read_irq_status();
    let next = (current & !IRQ_STATUS_FAULT_CLEAR_EVENT_MASK) | ((value << IRQ_STATUS_FAULT_CLEAR_EVENT_SHIFT) & IRQ_STATUS_FAULT_CLEAR_EVENT_MASK);
    write_irq_status(next);
}

#[inline]
pub fn read_fault_status() -> u32 {
    read_reg(FAULT_STATUS_OFFSET)
}

#[inline]
pub fn get_fault_status_fault_code() -> u32 {
    (read_fault_status() & FAULT_STATUS_FAULT_CODE_MASK) >> FAULT_STATUS_FAULT_CODE_SHIFT
}

#[inline]
pub fn get_fault_status_fault_latched() -> u32 {
    (read_fault_status() & FAULT_STATUS_FAULT_LATCHED_MASK) >> FAULT_STATUS_FAULT_LATCHED_SHIFT
}

#[inline]
pub fn get_fault_status_safe_state() -> u32 {
    (read_fault_status() & FAULT_STATUS_SAFE_STATE_MASK) >> FAULT_STATUS_SAFE_STATE_SHIFT
}

