use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const CTRL_OFFSET: usize = 0x00000000;
pub const CTRL_COMMAND_VALID_SHIFT: u32 = 0;
pub const CTRL_COMMAND_VALID_WIDTH: u32 = 1;
pub const CTRL_COMMAND_VALID_MASK: u32 = 0x00000001;
pub const CTRL_CONTROL_MODE_SHIFT: u32 = 4;
pub const CTRL_CONTROL_MODE_WIDTH: u32 = 4;
pub const CTRL_CONTROL_MODE_MASK: u32 = 0x000000F0;
pub const CTRL_INTEGRITY_SHIFT: u32 = 8;
pub const CTRL_INTEGRITY_WIDTH: u32 = 4;
pub const CTRL_INTEGRITY_MASK: u32 = 0x00000F00;
pub const CMD_ID_SEQ_OFFSET: usize = 0x00000004;
pub const CMD_ID_SEQ_COMMAND_ID_SHIFT: u32 = 0;
pub const CMD_ID_SEQ_COMMAND_ID_WIDTH: u32 = 8;
pub const CMD_ID_SEQ_COMMAND_ID_MASK: u32 = 0x000000FF;
pub const CMD_ID_SEQ_SEQUENCE_NUMBER_SHIFT: u32 = 8;
pub const CMD_ID_SEQ_SEQUENCE_NUMBER_WIDTH: u32 = 16;
pub const CMD_ID_SEQ_SEQUENCE_NUMBER_MASK: u32 = 0x00FFFF00;
pub const CMD_ID_SEQ_AGE_OR_TIMESTAMP_SHIFT: u32 = 24;
pub const CMD_ID_SEQ_AGE_OR_TIMESTAMP_WIDTH: u32 = 8;
pub const CMD_ID_SEQ_AGE_OR_TIMESTAMP_MASK: u32 = 0xFF000000;
pub const CMD_POS_OFFSET: usize = 0x00000008;
pub const CMD_POS_REQUESTED_ACTUATOR_POSITION_SHIFT: u32 = 0;
pub const CMD_POS_REQUESTED_ACTUATOR_POSITION_WIDTH: u32 = 8;
pub const CMD_POS_REQUESTED_ACTUATOR_POSITION_MASK: u32 = 0x000000FF;
pub const CFG_TIMEOUT_OFFSET: usize = 0x0000000C;
pub const CFG_TIMEOUT_TIMEOUT_LIMIT_SHIFT: u32 = 0;
pub const CFG_TIMEOUT_TIMEOUT_LIMIT_WIDTH: u32 = 16;
pub const CFG_TIMEOUT_TIMEOUT_LIMIT_MASK: u32 = 0x0000FFFF;
pub const CFG_TIMEOUT_SEQ_POLICY_SHIFT: u32 = 16;
pub const CFG_TIMEOUT_SEQ_POLICY_WIDTH: u32 = 2;
pub const CFG_TIMEOUT_SEQ_POLICY_MASK: u32 = 0x00030000;
pub const CFG_TIMEOUT_CONTROL_MODE_PERMIT_SHIFT: u32 = 18;
pub const CFG_TIMEOUT_CONTROL_MODE_PERMIT_WIDTH: u32 = 4;
pub const CFG_TIMEOUT_CONTROL_MODE_PERMIT_MASK: u32 = 0x003C0000;
pub const CFG_LIMITS_OFFSET: usize = 0x00000010;
pub const CFG_LIMITS_ACT_MIN_SHIFT: u32 = 0;
pub const CFG_LIMITS_ACT_MIN_WIDTH: u32 = 8;
pub const CFG_LIMITS_ACT_MIN_MASK: u32 = 0x000000FF;
pub const CFG_LIMITS_ACT_MAX_SHIFT: u32 = 8;
pub const CFG_LIMITS_ACT_MAX_WIDTH: u32 = 8;
pub const CFG_LIMITS_ACT_MAX_MASK: u32 = 0x0000FF00;
pub const CFG_LIMITS_SAFE_MIN_SHIFT: u32 = 16;
pub const CFG_LIMITS_SAFE_MIN_WIDTH: u32 = 8;
pub const CFG_LIMITS_SAFE_MIN_MASK: u32 = 0x00FF0000;
pub const CFG_LIMITS_SAFE_MAX_SHIFT: u32 = 24;
pub const CFG_LIMITS_SAFE_MAX_WIDTH: u32 = 8;
pub const CFG_LIMITS_SAFE_MAX_MASK: u32 = 0xFF000000;
pub const IRQ_CTRL_OFFSET: usize = 0x00000014;
pub const IRQ_CTRL_IRQ_ENABLE_SHIFT: u32 = 0;
pub const IRQ_CTRL_IRQ_ENABLE_WIDTH: u32 = 4;
pub const IRQ_CTRL_IRQ_ENABLE_MASK: u32 = 0x0000000F;
pub const IRQ_CTRL_CLEAR_STICKY_FAULTS_SHIFT: u32 = 31;
pub const IRQ_CTRL_CLEAR_STICKY_FAULTS_WIDTH: u32 = 1;
pub const IRQ_CTRL_CLEAR_STICKY_FAULTS_MASK: u32 = 0x80000000;
pub const STATUS_OFFSET: usize = 0x00000018;
pub const STATUS_ACCEPTED_EVENT_SHIFT: u32 = 0;
pub const STATUS_ACCEPTED_EVENT_WIDTH: u32 = 1;
pub const STATUS_ACCEPTED_EVENT_MASK: u32 = 0x00000001;
pub const STATUS_REJECTED_EVENT_SHIFT: u32 = 1;
pub const STATUS_REJECTED_EVENT_WIDTH: u32 = 1;
pub const STATUS_REJECTED_EVENT_MASK: u32 = 0x00000002;
pub const STATUS_STALE_DATA_FAULT_SHIFT: u32 = 2;
pub const STATUS_STALE_DATA_FAULT_WIDTH: u32 = 1;
pub const STATUS_STALE_DATA_FAULT_MASK: u32 = 0x00000004;
pub const STATUS_TIMEOUT_FAULT_SHIFT: u32 = 3;
pub const STATUS_TIMEOUT_FAULT_WIDTH: u32 = 1;
pub const STATUS_TIMEOUT_FAULT_MASK: u32 = 0x00000008;
pub const STATUS_CLAMP_APPLIED_SHIFT: u32 = 4;
pub const STATUS_CLAMP_APPLIED_WIDTH: u32 = 1;
pub const STATUS_CLAMP_APPLIED_MASK: u32 = 0x00000010;
pub const STATUS_FALLBACK_ACTIVE_SHIFT: u32 = 5;
pub const STATUS_FALLBACK_ACTIVE_WIDTH: u32 = 1;
pub const STATUS_FALLBACK_ACTIVE_MASK: u32 = 0x00000020;
pub const STATUS_SEQUENCE_NUMBER_SEEN_SHIFT: u32 = 8;
pub const STATUS_SEQUENCE_NUMBER_SEEN_WIDTH: u32 = 16;
pub const STATUS_SEQUENCE_NUMBER_SEEN_MASK: u32 = 0x00FFFF00;
pub const STATUS_LAST_FAULT_CODE_SHIFT: u32 = 24;
pub const STATUS_LAST_FAULT_CODE_WIDTH: u32 = 8;
pub const STATUS_LAST_FAULT_CODE_MASK: u32 = 0xFF000000;
pub const WATCHDOG_OFFSET: usize = 0x0000001C;
pub const WATCHDOG_WATCHDOG_COUNT_SHIFT: u32 = 0;
pub const WATCHDOG_WATCHDOG_COUNT_WIDTH: u32 = 16;
pub const WATCHDOG_WATCHDOG_COUNT_MASK: u32 = 0x0000FFFF;
pub const WATCHDOG_STATUS_CAPTURE_VALID_SHIFT: u32 = 31;
pub const WATCHDOG_STATUS_CAPTURE_VALID_WIDTH: u32 = 1;
pub const WATCHDOG_STATUS_CAPTURE_VALID_MASK: u32 = 0x80000000;

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
pub fn get_ctrl_command_valid() -> u32 {
    (read_ctrl() & CTRL_COMMAND_VALID_MASK) >> CTRL_COMMAND_VALID_SHIFT
}

#[inline]
pub fn set_ctrl_command_valid(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_COMMAND_VALID_MASK) | ((value << CTRL_COMMAND_VALID_SHIFT) & CTRL_COMMAND_VALID_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_control_mode() -> u32 {
    (read_ctrl() & CTRL_CONTROL_MODE_MASK) >> CTRL_CONTROL_MODE_SHIFT
}

#[inline]
pub fn set_ctrl_control_mode(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_CONTROL_MODE_MASK) | ((value << CTRL_CONTROL_MODE_SHIFT) & CTRL_CONTROL_MODE_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_integrity() -> u32 {
    (read_ctrl() & CTRL_INTEGRITY_MASK) >> CTRL_INTEGRITY_SHIFT
}

#[inline]
pub fn set_ctrl_integrity(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_INTEGRITY_MASK) | ((value << CTRL_INTEGRITY_SHIFT) & CTRL_INTEGRITY_MASK);
    write_ctrl(next);
}

#[inline]
pub fn read_cmd_id_seq() -> u32 {
    read_reg(CMD_ID_SEQ_OFFSET)
}

#[inline]
pub fn write_cmd_id_seq(value: u32) {
    write_reg(CMD_ID_SEQ_OFFSET, value)
}

#[inline]
pub fn get_cmd_id_seq_command_id() -> u32 {
    (read_cmd_id_seq() & CMD_ID_SEQ_COMMAND_ID_MASK) >> CMD_ID_SEQ_COMMAND_ID_SHIFT
}

#[inline]
pub fn set_cmd_id_seq_command_id(value: u32) {
    let current = read_cmd_id_seq();
    let next = (current & !CMD_ID_SEQ_COMMAND_ID_MASK) | ((value << CMD_ID_SEQ_COMMAND_ID_SHIFT) & CMD_ID_SEQ_COMMAND_ID_MASK);
    write_cmd_id_seq(next);
}

#[inline]
pub fn get_cmd_id_seq_sequence_number() -> u32 {
    (read_cmd_id_seq() & CMD_ID_SEQ_SEQUENCE_NUMBER_MASK) >> CMD_ID_SEQ_SEQUENCE_NUMBER_SHIFT
}

#[inline]
pub fn set_cmd_id_seq_sequence_number(value: u32) {
    let current = read_cmd_id_seq();
    let next = (current & !CMD_ID_SEQ_SEQUENCE_NUMBER_MASK) | ((value << CMD_ID_SEQ_SEQUENCE_NUMBER_SHIFT) & CMD_ID_SEQ_SEQUENCE_NUMBER_MASK);
    write_cmd_id_seq(next);
}

#[inline]
pub fn get_cmd_id_seq_age_or_timestamp() -> u32 {
    (read_cmd_id_seq() & CMD_ID_SEQ_AGE_OR_TIMESTAMP_MASK) >> CMD_ID_SEQ_AGE_OR_TIMESTAMP_SHIFT
}

#[inline]
pub fn set_cmd_id_seq_age_or_timestamp(value: u32) {
    let current = read_cmd_id_seq();
    let next = (current & !CMD_ID_SEQ_AGE_OR_TIMESTAMP_MASK) | ((value << CMD_ID_SEQ_AGE_OR_TIMESTAMP_SHIFT) & CMD_ID_SEQ_AGE_OR_TIMESTAMP_MASK);
    write_cmd_id_seq(next);
}

#[inline]
pub fn read_cmd_pos() -> u32 {
    read_reg(CMD_POS_OFFSET)
}

#[inline]
pub fn write_cmd_pos(value: u32) {
    write_reg(CMD_POS_OFFSET, value)
}

#[inline]
pub fn get_cmd_pos_requested_actuator_position() -> u32 {
    (read_cmd_pos() & CMD_POS_REQUESTED_ACTUATOR_POSITION_MASK) >> CMD_POS_REQUESTED_ACTUATOR_POSITION_SHIFT
}

#[inline]
pub fn set_cmd_pos_requested_actuator_position(value: u32) {
    let current = read_cmd_pos();
    let next = (current & !CMD_POS_REQUESTED_ACTUATOR_POSITION_MASK) | ((value << CMD_POS_REQUESTED_ACTUATOR_POSITION_SHIFT) & CMD_POS_REQUESTED_ACTUATOR_POSITION_MASK);
    write_cmd_pos(next);
}

#[inline]
pub fn read_cfg_timeout() -> u32 {
    read_reg(CFG_TIMEOUT_OFFSET)
}

#[inline]
pub fn write_cfg_timeout(value: u32) {
    write_reg(CFG_TIMEOUT_OFFSET, value)
}

#[inline]
pub fn get_cfg_timeout_timeout_limit() -> u32 {
    (read_cfg_timeout() & CFG_TIMEOUT_TIMEOUT_LIMIT_MASK) >> CFG_TIMEOUT_TIMEOUT_LIMIT_SHIFT
}

#[inline]
pub fn set_cfg_timeout_timeout_limit(value: u32) {
    let current = read_cfg_timeout();
    let next = (current & !CFG_TIMEOUT_TIMEOUT_LIMIT_MASK) | ((value << CFG_TIMEOUT_TIMEOUT_LIMIT_SHIFT) & CFG_TIMEOUT_TIMEOUT_LIMIT_MASK);
    write_cfg_timeout(next);
}

#[inline]
pub fn get_cfg_timeout_seq_policy() -> u32 {
    (read_cfg_timeout() & CFG_TIMEOUT_SEQ_POLICY_MASK) >> CFG_TIMEOUT_SEQ_POLICY_SHIFT
}

#[inline]
pub fn set_cfg_timeout_seq_policy(value: u32) {
    let current = read_cfg_timeout();
    let next = (current & !CFG_TIMEOUT_SEQ_POLICY_MASK) | ((value << CFG_TIMEOUT_SEQ_POLICY_SHIFT) & CFG_TIMEOUT_SEQ_POLICY_MASK);
    write_cfg_timeout(next);
}

#[inline]
pub fn get_cfg_timeout_control_mode_permit() -> u32 {
    (read_cfg_timeout() & CFG_TIMEOUT_CONTROL_MODE_PERMIT_MASK) >> CFG_TIMEOUT_CONTROL_MODE_PERMIT_SHIFT
}

#[inline]
pub fn set_cfg_timeout_control_mode_permit(value: u32) {
    let current = read_cfg_timeout();
    let next = (current & !CFG_TIMEOUT_CONTROL_MODE_PERMIT_MASK) | ((value << CFG_TIMEOUT_CONTROL_MODE_PERMIT_SHIFT) & CFG_TIMEOUT_CONTROL_MODE_PERMIT_MASK);
    write_cfg_timeout(next);
}

#[inline]
pub fn read_cfg_limits() -> u32 {
    read_reg(CFG_LIMITS_OFFSET)
}

#[inline]
pub fn write_cfg_limits(value: u32) {
    write_reg(CFG_LIMITS_OFFSET, value)
}

#[inline]
pub fn get_cfg_limits_act_min() -> u32 {
    (read_cfg_limits() & CFG_LIMITS_ACT_MIN_MASK) >> CFG_LIMITS_ACT_MIN_SHIFT
}

#[inline]
pub fn set_cfg_limits_act_min(value: u32) {
    let current = read_cfg_limits();
    let next = (current & !CFG_LIMITS_ACT_MIN_MASK) | ((value << CFG_LIMITS_ACT_MIN_SHIFT) & CFG_LIMITS_ACT_MIN_MASK);
    write_cfg_limits(next);
}

#[inline]
pub fn get_cfg_limits_act_max() -> u32 {
    (read_cfg_limits() & CFG_LIMITS_ACT_MAX_MASK) >> CFG_LIMITS_ACT_MAX_SHIFT
}

#[inline]
pub fn set_cfg_limits_act_max(value: u32) {
    let current = read_cfg_limits();
    let next = (current & !CFG_LIMITS_ACT_MAX_MASK) | ((value << CFG_LIMITS_ACT_MAX_SHIFT) & CFG_LIMITS_ACT_MAX_MASK);
    write_cfg_limits(next);
}

#[inline]
pub fn get_cfg_limits_safe_min() -> u32 {
    (read_cfg_limits() & CFG_LIMITS_SAFE_MIN_MASK) >> CFG_LIMITS_SAFE_MIN_SHIFT
}

#[inline]
pub fn set_cfg_limits_safe_min(value: u32) {
    let current = read_cfg_limits();
    let next = (current & !CFG_LIMITS_SAFE_MIN_MASK) | ((value << CFG_LIMITS_SAFE_MIN_SHIFT) & CFG_LIMITS_SAFE_MIN_MASK);
    write_cfg_limits(next);
}

#[inline]
pub fn get_cfg_limits_safe_max() -> u32 {
    (read_cfg_limits() & CFG_LIMITS_SAFE_MAX_MASK) >> CFG_LIMITS_SAFE_MAX_SHIFT
}

#[inline]
pub fn set_cfg_limits_safe_max(value: u32) {
    let current = read_cfg_limits();
    let next = (current & !CFG_LIMITS_SAFE_MAX_MASK) | ((value << CFG_LIMITS_SAFE_MAX_SHIFT) & CFG_LIMITS_SAFE_MAX_MASK);
    write_cfg_limits(next);
}

#[inline]
pub fn read_irq_ctrl() -> u32 {
    read_reg(IRQ_CTRL_OFFSET)
}

#[inline]
pub fn write_irq_ctrl(value: u32) {
    write_reg(IRQ_CTRL_OFFSET, value)
}

#[inline]
pub fn get_irq_ctrl_irq_enable() -> u32 {
    (read_irq_ctrl() & IRQ_CTRL_IRQ_ENABLE_MASK) >> IRQ_CTRL_IRQ_ENABLE_SHIFT
}

#[inline]
pub fn set_irq_ctrl_irq_enable(value: u32) {
    let current = read_irq_ctrl();
    let next = (current & !IRQ_CTRL_IRQ_ENABLE_MASK) | ((value << IRQ_CTRL_IRQ_ENABLE_SHIFT) & IRQ_CTRL_IRQ_ENABLE_MASK);
    write_irq_ctrl(next);
}

#[inline]
pub fn get_irq_ctrl_clear_sticky_faults() -> u32 {
    (read_irq_ctrl() & IRQ_CTRL_CLEAR_STICKY_FAULTS_MASK) >> IRQ_CTRL_CLEAR_STICKY_FAULTS_SHIFT
}

#[inline]
pub fn set_irq_ctrl_clear_sticky_faults(value: u32) {
    let current = read_irq_ctrl();
    let next = (current & !IRQ_CTRL_CLEAR_STICKY_FAULTS_MASK) | ((value << IRQ_CTRL_CLEAR_STICKY_FAULTS_SHIFT) & IRQ_CTRL_CLEAR_STICKY_FAULTS_MASK);
    write_irq_ctrl(next);
}

#[inline]
pub fn read_status() -> u32 {
    read_reg(STATUS_OFFSET)
}

#[inline]
pub fn get_status_accepted_event() -> u32 {
    (read_status() & STATUS_ACCEPTED_EVENT_MASK) >> STATUS_ACCEPTED_EVENT_SHIFT
}

#[inline]
pub fn get_status_rejected_event() -> u32 {
    (read_status() & STATUS_REJECTED_EVENT_MASK) >> STATUS_REJECTED_EVENT_SHIFT
}

#[inline]
pub fn get_status_stale_data_fault() -> u32 {
    (read_status() & STATUS_STALE_DATA_FAULT_MASK) >> STATUS_STALE_DATA_FAULT_SHIFT
}

#[inline]
pub fn get_status_timeout_fault() -> u32 {
    (read_status() & STATUS_TIMEOUT_FAULT_MASK) >> STATUS_TIMEOUT_FAULT_SHIFT
}

#[inline]
pub fn get_status_clamp_applied() -> u32 {
    (read_status() & STATUS_CLAMP_APPLIED_MASK) >> STATUS_CLAMP_APPLIED_SHIFT
}

#[inline]
pub fn get_status_fallback_active() -> u32 {
    (read_status() & STATUS_FALLBACK_ACTIVE_MASK) >> STATUS_FALLBACK_ACTIVE_SHIFT
}

#[inline]
pub fn get_status_sequence_number_seen() -> u32 {
    (read_status() & STATUS_SEQUENCE_NUMBER_SEEN_MASK) >> STATUS_SEQUENCE_NUMBER_SEEN_SHIFT
}

#[inline]
pub fn get_status_last_fault_code() -> u32 {
    (read_status() & STATUS_LAST_FAULT_CODE_MASK) >> STATUS_LAST_FAULT_CODE_SHIFT
}

#[inline]
pub fn read_watchdog() -> u32 {
    read_reg(WATCHDOG_OFFSET)
}

#[inline]
pub fn get_watchdog_watchdog_count() -> u32 {
    (read_watchdog() & WATCHDOG_WATCHDOG_COUNT_MASK) >> WATCHDOG_WATCHDOG_COUNT_SHIFT
}

#[inline]
pub fn get_watchdog_status_capture_valid() -> u32 {
    (read_watchdog() & WATCHDOG_STATUS_CAPTURE_VALID_MASK) >> WATCHDOG_STATUS_CAPTURE_VALID_SHIFT
}

