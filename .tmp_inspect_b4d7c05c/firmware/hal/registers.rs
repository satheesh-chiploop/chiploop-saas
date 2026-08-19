use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const CTRL_OFFSET: usize = 0x00000000;
pub const CTRL_START_REQUEST_SHIFT: u32 = 0;
pub const CTRL_START_REQUEST_WIDTH: u32 = 1;
pub const CTRL_START_REQUEST_MASK: u32 = 0x00000001;
pub const CTRL_CLEAR_FAULTS_SHIFT: u32 = 1;
pub const CTRL_CLEAR_FAULTS_WIDTH: u32 = 1;
pub const CTRL_CLEAR_FAULTS_MASK: u32 = 0x00000002;
pub const CTRL_SAFE_MODE_SELECT_SHIFT: u32 = 2;
pub const CTRL_SAFE_MODE_SELECT_WIDTH: u32 = 1;
pub const CTRL_SAFE_MODE_SELECT_MASK: u32 = 0x00000004;
pub const REQUEST_OFFSET: usize = 0x00000004;
pub const REQUEST_REQUEST_SEQ_SHIFT: u32 = 0;
pub const REQUEST_REQUEST_SEQ_WIDTH: u32 = 16;
pub const REQUEST_REQUEST_SEQ_MASK: u32 = 0x0000FFFF;
pub const REQUEST_FLOW_CONDITION_SEL_SHIFT: u32 = 16;
pub const REQUEST_FLOW_CONDITION_SEL_WIDTH: u32 = 4;
pub const REQUEST_FLOW_CONDITION_SEL_MASK: u32 = 0x000F0000;
pub const REQUEST_CONTROL_MODE_SHIFT: u32 = 20;
pub const REQUEST_CONTROL_MODE_WIDTH: u32 = 4;
pub const REQUEST_CONTROL_MODE_MASK: u32 = 0x00F00000;
pub const REQUEST_VELOCITY_OFFSET: usize = 0x00000008;
pub const REQUEST_VELOCITY_STREAM_VELOCITY_SHIFT: u32 = 0;
pub const REQUEST_VELOCITY_STREAM_VELOCITY_WIDTH: u32 = 32;
pub const REQUEST_VELOCITY_STREAM_VELOCITY_MASK: u32 = 0xFFFFFFFF;
pub const GEOMETRY_OFFSET: usize = 0x0000000C;
pub const GEOMETRY_GEOMETRY_ID_SHIFT: u32 = 0;
pub const GEOMETRY_GEOMETRY_ID_WIDTH: u32 = 16;
pub const GEOMETRY_GEOMETRY_ID_MASK: u32 = 0x0000FFFF;
pub const TIMEOUT_CYCLES_OFFSET: usize = 0x00000010;
pub const TIMEOUT_CYCLES_TIMEOUT_CYCLES_SHIFT: u32 = 0;
pub const TIMEOUT_CYCLES_TIMEOUT_CYCLES_WIDTH: u32 = 32;
pub const TIMEOUT_CYCLES_TIMEOUT_CYCLES_MASK: u32 = 0xFFFFFFFF;
pub const FRESHNESS_CYCLES_OFFSET: usize = 0x00000014;
pub const FRESHNESS_CYCLES_FRESHNESS_CYCLES_SHIFT: u32 = 0;
pub const FRESHNESS_CYCLES_FRESHNESS_CYCLES_WIDTH: u32 = 32;
pub const FRESHNESS_CYCLES_FRESHNESS_CYCLES_MASK: u32 = 0xFFFFFFFF;
pub const ACTUATOR_MIN_OFFSET: usize = 0x00000018;
pub const ACTUATOR_MIN_ACTUATOR_MIN_SHIFT: u32 = 0;
pub const ACTUATOR_MIN_ACTUATOR_MIN_WIDTH: u32 = 32;
pub const ACTUATOR_MIN_ACTUATOR_MIN_MASK: u32 = 0xFFFFFFFF;
pub const ACTUATOR_MAX_OFFSET: usize = 0x0000001C;
pub const ACTUATOR_MAX_ACTUATOR_MAX_SHIFT: u32 = 0;
pub const ACTUATOR_MAX_ACTUATOR_MAX_WIDTH: u32 = 32;
pub const ACTUATOR_MAX_ACTUATOR_MAX_MASK: u32 = 0xFFFFFFFF;
pub const RATE_LIMIT_OFFSET: usize = 0x00000020;
pub const RATE_LIMIT_RATE_LIMIT_SHIFT: u32 = 0;
pub const RATE_LIMIT_RATE_LIMIT_WIDTH: u32 = 32;
pub const RATE_LIMIT_RATE_LIMIT_MASK: u32 = 0xFFFFFFFF;
pub const STATUS_OFFSET: usize = 0x00000024;
pub const STATUS_BUSY_SHIFT: u32 = 0;
pub const STATUS_BUSY_WIDTH: u32 = 1;
pub const STATUS_BUSY_MASK: u32 = 0x00000001;
pub const STATUS_RESPONSE_VALID_SHIFT: u32 = 1;
pub const STATUS_RESPONSE_VALID_WIDTH: u32 = 1;
pub const STATUS_RESPONSE_VALID_MASK: u32 = 0x00000002;
pub const STATUS_TIMEOUT_FAULT_SHIFT: u32 = 2;
pub const STATUS_TIMEOUT_FAULT_WIDTH: u32 = 1;
pub const STATUS_TIMEOUT_FAULT_MASK: u32 = 0x00000004;
pub const STATUS_STALE_FAULT_SHIFT: u32 = 3;
pub const STATUS_STALE_FAULT_WIDTH: u32 = 1;
pub const STATUS_STALE_FAULT_MASK: u32 = 0x00000008;
pub const STATUS_RESPONSE_SEQ_MISMATCH_SHIFT: u32 = 4;
pub const STATUS_RESPONSE_SEQ_MISMATCH_WIDTH: u32 = 1;
pub const STATUS_RESPONSE_SEQ_MISMATCH_MASK: u32 = 0x00000010;
pub const STATUS_INVALID_PAYLOAD_FAULT_SHIFT: u32 = 5;
pub const STATUS_INVALID_PAYLOAD_FAULT_WIDTH: u32 = 1;
pub const STATUS_INVALID_PAYLOAD_FAULT_MASK: u32 = 0x00000020;
pub const STATUS_FALLBACK_ACTIVE_SHIFT: u32 = 6;
pub const STATUS_FALLBACK_ACTIVE_WIDTH: u32 = 1;
pub const STATUS_FALLBACK_ACTIVE_MASK: u32 = 0x00000040;
pub const STATUS_FAULT_PENDING_SHIFT: u32 = 7;
pub const STATUS_FAULT_PENDING_WIDTH: u32 = 1;
pub const STATUS_FAULT_PENDING_MASK: u32 = 0x00000080;
pub const SEQUENCE_OFFSET: usize = 0x00000028;
pub const SEQUENCE_CURRENT_SEQUENCE_SHIFT: u32 = 0;
pub const SEQUENCE_CURRENT_SEQUENCE_WIDTH: u32 = 16;
pub const SEQUENCE_CURRENT_SEQUENCE_MASK: u32 = 0x0000FFFF;
pub const SEQUENCE_LAST_GOOD_COMMAND_SHIFT: u32 = 16;
pub const SEQUENCE_LAST_GOOD_COMMAND_WIDTH: u32 = 16;
pub const SEQUENCE_LAST_GOOD_COMMAND_MASK: u32 = 0xFFFF0000;
pub const LAST_GOOD_COMMAND_OFFSET: usize = 0x0000002C;
pub const LAST_GOOD_COMMAND_LAST_GOOD_COMMAND_SHIFT: u32 = 0;
pub const LAST_GOOD_COMMAND_LAST_GOOD_COMMAND_WIDTH: u32 = 32;
pub const LAST_GOOD_COMMAND_LAST_GOOD_COMMAND_MASK: u32 = 0xFFFFFFFF;

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
pub fn get_ctrl_start_request() -> u32 {
    (read_ctrl() & CTRL_START_REQUEST_MASK) >> CTRL_START_REQUEST_SHIFT
}

#[inline]
pub fn set_ctrl_start_request(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_START_REQUEST_MASK) | ((value << CTRL_START_REQUEST_SHIFT) & CTRL_START_REQUEST_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_clear_faults() -> u32 {
    (read_ctrl() & CTRL_CLEAR_FAULTS_MASK) >> CTRL_CLEAR_FAULTS_SHIFT
}

#[inline]
pub fn set_ctrl_clear_faults(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_CLEAR_FAULTS_MASK) | ((value << CTRL_CLEAR_FAULTS_SHIFT) & CTRL_CLEAR_FAULTS_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_safe_mode_select() -> u32 {
    (read_ctrl() & CTRL_SAFE_MODE_SELECT_MASK) >> CTRL_SAFE_MODE_SELECT_SHIFT
}

#[inline]
pub fn set_ctrl_safe_mode_select(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_SAFE_MODE_SELECT_MASK) | ((value << CTRL_SAFE_MODE_SELECT_SHIFT) & CTRL_SAFE_MODE_SELECT_MASK);
    write_ctrl(next);
}

#[inline]
pub fn read_request() -> u32 {
    read_reg(REQUEST_OFFSET)
}

#[inline]
pub fn write_request(value: u32) {
    write_reg(REQUEST_OFFSET, value)
}

#[inline]
pub fn get_request_request_seq() -> u32 {
    (read_request() & REQUEST_REQUEST_SEQ_MASK) >> REQUEST_REQUEST_SEQ_SHIFT
}

#[inline]
pub fn set_request_request_seq(value: u32) {
    let current = read_request();
    let next = (current & !REQUEST_REQUEST_SEQ_MASK) | ((value << REQUEST_REQUEST_SEQ_SHIFT) & REQUEST_REQUEST_SEQ_MASK);
    write_request(next);
}

#[inline]
pub fn get_request_flow_condition_sel() -> u32 {
    (read_request() & REQUEST_FLOW_CONDITION_SEL_MASK) >> REQUEST_FLOW_CONDITION_SEL_SHIFT
}

#[inline]
pub fn set_request_flow_condition_sel(value: u32) {
    let current = read_request();
    let next = (current & !REQUEST_FLOW_CONDITION_SEL_MASK) | ((value << REQUEST_FLOW_CONDITION_SEL_SHIFT) & REQUEST_FLOW_CONDITION_SEL_MASK);
    write_request(next);
}

#[inline]
pub fn get_request_control_mode() -> u32 {
    (read_request() & REQUEST_CONTROL_MODE_MASK) >> REQUEST_CONTROL_MODE_SHIFT
}

#[inline]
pub fn set_request_control_mode(value: u32) {
    let current = read_request();
    let next = (current & !REQUEST_CONTROL_MODE_MASK) | ((value << REQUEST_CONTROL_MODE_SHIFT) & REQUEST_CONTROL_MODE_MASK);
    write_request(next);
}

#[inline]
pub fn read_request_velocity() -> u32 {
    read_reg(REQUEST_VELOCITY_OFFSET)
}

#[inline]
pub fn write_request_velocity(value: u32) {
    write_reg(REQUEST_VELOCITY_OFFSET, value)
}

#[inline]
pub fn get_request_velocity_stream_velocity() -> u32 {
    (read_request_velocity() & REQUEST_VELOCITY_STREAM_VELOCITY_MASK) >> REQUEST_VELOCITY_STREAM_VELOCITY_SHIFT
}

#[inline]
pub fn set_request_velocity_stream_velocity(value: u32) {
    let current = read_request_velocity();
    let next = (current & !REQUEST_VELOCITY_STREAM_VELOCITY_MASK) | ((value << REQUEST_VELOCITY_STREAM_VELOCITY_SHIFT) & REQUEST_VELOCITY_STREAM_VELOCITY_MASK);
    write_request_velocity(next);
}

#[inline]
pub fn read_geometry() -> u32 {
    read_reg(GEOMETRY_OFFSET)
}

#[inline]
pub fn write_geometry(value: u32) {
    write_reg(GEOMETRY_OFFSET, value)
}

#[inline]
pub fn get_geometry_geometry_id() -> u32 {
    (read_geometry() & GEOMETRY_GEOMETRY_ID_MASK) >> GEOMETRY_GEOMETRY_ID_SHIFT
}

#[inline]
pub fn set_geometry_geometry_id(value: u32) {
    let current = read_geometry();
    let next = (current & !GEOMETRY_GEOMETRY_ID_MASK) | ((value << GEOMETRY_GEOMETRY_ID_SHIFT) & GEOMETRY_GEOMETRY_ID_MASK);
    write_geometry(next);
}

#[inline]
pub fn read_timeout_cycles() -> u32 {
    read_reg(TIMEOUT_CYCLES_OFFSET)
}

#[inline]
pub fn write_timeout_cycles(value: u32) {
    write_reg(TIMEOUT_CYCLES_OFFSET, value)
}

#[inline]
pub fn get_timeout_cycles_timeout_cycles() -> u32 {
    (read_timeout_cycles() & TIMEOUT_CYCLES_TIMEOUT_CYCLES_MASK) >> TIMEOUT_CYCLES_TIMEOUT_CYCLES_SHIFT
}

#[inline]
pub fn set_timeout_cycles_timeout_cycles(value: u32) {
    let current = read_timeout_cycles();
    let next = (current & !TIMEOUT_CYCLES_TIMEOUT_CYCLES_MASK) | ((value << TIMEOUT_CYCLES_TIMEOUT_CYCLES_SHIFT) & TIMEOUT_CYCLES_TIMEOUT_CYCLES_MASK);
    write_timeout_cycles(next);
}

#[inline]
pub fn read_freshness_cycles() -> u32 {
    read_reg(FRESHNESS_CYCLES_OFFSET)
}

#[inline]
pub fn write_freshness_cycles(value: u32) {
    write_reg(FRESHNESS_CYCLES_OFFSET, value)
}

#[inline]
pub fn get_freshness_cycles_freshness_cycles() -> u32 {
    (read_freshness_cycles() & FRESHNESS_CYCLES_FRESHNESS_CYCLES_MASK) >> FRESHNESS_CYCLES_FRESHNESS_CYCLES_SHIFT
}

#[inline]
pub fn set_freshness_cycles_freshness_cycles(value: u32) {
    let current = read_freshness_cycles();
    let next = (current & !FRESHNESS_CYCLES_FRESHNESS_CYCLES_MASK) | ((value << FRESHNESS_CYCLES_FRESHNESS_CYCLES_SHIFT) & FRESHNESS_CYCLES_FRESHNESS_CYCLES_MASK);
    write_freshness_cycles(next);
}

#[inline]
pub fn read_actuator_min() -> u32 {
    read_reg(ACTUATOR_MIN_OFFSET)
}

#[inline]
pub fn write_actuator_min(value: u32) {
    write_reg(ACTUATOR_MIN_OFFSET, value)
}

#[inline]
pub fn get_actuator_min_actuator_min() -> u32 {
    (read_actuator_min() & ACTUATOR_MIN_ACTUATOR_MIN_MASK) >> ACTUATOR_MIN_ACTUATOR_MIN_SHIFT
}

#[inline]
pub fn set_actuator_min_actuator_min(value: u32) {
    let current = read_actuator_min();
    let next = (current & !ACTUATOR_MIN_ACTUATOR_MIN_MASK) | ((value << ACTUATOR_MIN_ACTUATOR_MIN_SHIFT) & ACTUATOR_MIN_ACTUATOR_MIN_MASK);
    write_actuator_min(next);
}

#[inline]
pub fn read_actuator_max() -> u32 {
    read_reg(ACTUATOR_MAX_OFFSET)
}

#[inline]
pub fn write_actuator_max(value: u32) {
    write_reg(ACTUATOR_MAX_OFFSET, value)
}

#[inline]
pub fn get_actuator_max_actuator_max() -> u32 {
    (read_actuator_max() & ACTUATOR_MAX_ACTUATOR_MAX_MASK) >> ACTUATOR_MAX_ACTUATOR_MAX_SHIFT
}

#[inline]
pub fn set_actuator_max_actuator_max(value: u32) {
    let current = read_actuator_max();
    let next = (current & !ACTUATOR_MAX_ACTUATOR_MAX_MASK) | ((value << ACTUATOR_MAX_ACTUATOR_MAX_SHIFT) & ACTUATOR_MAX_ACTUATOR_MAX_MASK);
    write_actuator_max(next);
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
pub fn read_status() -> u32 {
    read_reg(STATUS_OFFSET)
}

#[inline]
pub fn get_status_busy() -> u32 {
    (read_status() & STATUS_BUSY_MASK) >> STATUS_BUSY_SHIFT
}

#[inline]
pub fn get_status_response_valid() -> u32 {
    (read_status() & STATUS_RESPONSE_VALID_MASK) >> STATUS_RESPONSE_VALID_SHIFT
}

#[inline]
pub fn get_status_timeout_fault() -> u32 {
    (read_status() & STATUS_TIMEOUT_FAULT_MASK) >> STATUS_TIMEOUT_FAULT_SHIFT
}

#[inline]
pub fn get_status_stale_fault() -> u32 {
    (read_status() & STATUS_STALE_FAULT_MASK) >> STATUS_STALE_FAULT_SHIFT
}

#[inline]
pub fn get_status_response_seq_mismatch() -> u32 {
    (read_status() & STATUS_RESPONSE_SEQ_MISMATCH_MASK) >> STATUS_RESPONSE_SEQ_MISMATCH_SHIFT
}

#[inline]
pub fn get_status_invalid_payload_fault() -> u32 {
    (read_status() & STATUS_INVALID_PAYLOAD_FAULT_MASK) >> STATUS_INVALID_PAYLOAD_FAULT_SHIFT
}

#[inline]
pub fn get_status_fallback_active() -> u32 {
    (read_status() & STATUS_FALLBACK_ACTIVE_MASK) >> STATUS_FALLBACK_ACTIVE_SHIFT
}

#[inline]
pub fn get_status_fault_pending() -> u32 {
    (read_status() & STATUS_FAULT_PENDING_MASK) >> STATUS_FAULT_PENDING_SHIFT
}

#[inline]
pub fn read_sequence() -> u32 {
    read_reg(SEQUENCE_OFFSET)
}

#[inline]
pub fn get_sequence_current_sequence() -> u32 {
    (read_sequence() & SEQUENCE_CURRENT_SEQUENCE_MASK) >> SEQUENCE_CURRENT_SEQUENCE_SHIFT
}

#[inline]
pub fn get_sequence_last_good_command() -> u32 {
    (read_sequence() & SEQUENCE_LAST_GOOD_COMMAND_MASK) >> SEQUENCE_LAST_GOOD_COMMAND_SHIFT
}

#[inline]
pub fn read_last_good_command() -> u32 {
    read_reg(LAST_GOOD_COMMAND_OFFSET)
}

#[inline]
pub fn get_last_good_command_last_good_command() -> u32 {
    (read_last_good_command() & LAST_GOOD_COMMAND_LAST_GOOD_COMMAND_MASK) >> LAST_GOOD_COMMAND_LAST_GOOD_COMMAND_SHIFT
}

