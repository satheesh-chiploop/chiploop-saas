use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const CONTROL_OFFSET: usize = 0x00000000;
pub const CONTROL_ENABLE_SHIFT: u32 = 0;
pub const CONTROL_ENABLE_WIDTH: u32 = 1;
pub const CONTROL_ENABLE_MASK: u32 = 0x00000001;
pub const CONTROL_CLEAR_FAULTS_SHIFT: u32 = 1;
pub const CONTROL_CLEAR_FAULTS_WIDTH: u32 = 1;
pub const CONTROL_CLEAR_FAULTS_MASK: u32 = 0x00000002;
pub const CONTROL_ARM_SAFE_FALLBACK_SHIFT: u32 = 2;
pub const CONTROL_ARM_SAFE_FALLBACK_WIDTH: u32 = 1;
pub const CONTROL_ARM_SAFE_FALLBACK_MASK: u32 = 0x00000004;
pub const CONTROL_BYPASS_OUTPUT_HOLD_SHIFT: u32 = 3;
pub const CONTROL_BYPASS_OUTPUT_HOLD_WIDTH: u32 = 1;
pub const CONTROL_BYPASS_OUTPUT_HOLD_MASK: u32 = 0x00000008;
pub const CONTROL_MODE_SHIFT: u32 = 4;
pub const CONTROL_MODE_WIDTH: u32 = 4;
pub const CONTROL_MODE_MASK: u32 = 0x000000F0;
pub const CONTROL_RESERVED_SHIFT: u32 = 8;
pub const CONTROL_RESERVED_WIDTH: u32 = 24;
pub const CONTROL_RESERVED_MASK: u32 = 0xFFFFFF00;
pub const STATUS_OFFSET: usize = 0x00000004;
pub const STATUS_BUSY_SHIFT: u32 = 0;
pub const STATUS_BUSY_WIDTH: u32 = 1;
pub const STATUS_BUSY_MASK: u32 = 0x00000001;
pub const STATUS_COMMAND_ACCEPTED_SHIFT: u32 = 1;
pub const STATUS_COMMAND_ACCEPTED_WIDTH: u32 = 1;
pub const STATUS_COMMAND_ACCEPTED_MASK: u32 = 0x00000002;
pub const STATUS_STALE_REJECTED_SHIFT: u32 = 2;
pub const STATUS_STALE_REJECTED_WIDTH: u32 = 1;
pub const STATUS_STALE_REJECTED_MASK: u32 = 0x00000004;
pub const STATUS_TIMEOUT_FAULT_SHIFT: u32 = 3;
pub const STATUS_TIMEOUT_FAULT_WIDTH: u32 = 1;
pub const STATUS_TIMEOUT_FAULT_MASK: u32 = 0x00000008;
pub const STATUS_INVALID_INPUT_SHIFT: u32 = 4;
pub const STATUS_INVALID_INPUT_WIDTH: u32 = 1;
pub const STATUS_INVALID_INPUT_MASK: u32 = 0x00000010;
pub const STATUS_CLAMP_APPLIED_SHIFT: u32 = 5;
pub const STATUS_CLAMP_APPLIED_WIDTH: u32 = 1;
pub const STATUS_CLAMP_APPLIED_MASK: u32 = 0x00000020;
pub const STATUS_SAFE_FALLBACK_ACTIVE_SHIFT: u32 = 6;
pub const STATUS_SAFE_FALLBACK_ACTIVE_WIDTH: u32 = 1;
pub const STATUS_SAFE_FALLBACK_ACTIVE_MASK: u32 = 0x00000040;
pub const STATUS_IRQ_PENDING_SHIFT: u32 = 7;
pub const STATUS_IRQ_PENDING_WIDTH: u32 = 1;
pub const STATUS_IRQ_PENDING_MASK: u32 = 0x00000080;
pub const STATUS_RESERVED_SHIFT: u32 = 8;
pub const STATUS_RESERVED_WIDTH: u32 = 24;
pub const STATUS_RESERVED_MASK: u32 = 0xFFFFFF00;
pub const SEQ_IN_OFFSET: usize = 0x00000008;
pub const SEQ_IN_SEQUENCE_NUMBER_SHIFT: u32 = 0;
pub const SEQ_IN_SEQUENCE_NUMBER_WIDTH: u32 = 32;
pub const SEQ_IN_SEQUENCE_NUMBER_MASK: u32 = 0xFFFFFFFF;
pub const AGE_LIMIT_OFFSET: usize = 0x0000000C;
pub const AGE_LIMIT_MAX_AGE_CYCLES_SHIFT: u32 = 0;
pub const AGE_LIMIT_MAX_AGE_CYCLES_WIDTH: u32 = 32;
pub const AGE_LIMIT_MAX_AGE_CYCLES_MASK: u32 = 0xFFFFFFFF;
pub const VELOCITY_MPS_OFFSET: usize = 0x00000010;
pub const VELOCITY_MPS_VELOCITY_FIXED_POINT_SHIFT: u32 = 0;
pub const VELOCITY_MPS_VELOCITY_FIXED_POINT_WIDTH: u32 = 32;
pub const VELOCITY_MPS_VELOCITY_FIXED_POINT_MASK: u32 = 0xFFFFFFFF;
pub const ACT_MIN_OFFSET: usize = 0x00000014;
pub const ACT_MIN_PACKED_MINIMUM_SHIFT: u32 = 0;
pub const ACT_MIN_PACKED_MINIMUM_WIDTH: u32 = 32;
pub const ACT_MIN_PACKED_MINIMUM_MASK: u32 = 0xFFFFFFFF;
pub const ACT_MAX_OFFSET: usize = 0x00000018;
pub const ACT_MAX_PACKED_MAXIMUM_SHIFT: u32 = 0;
pub const ACT_MAX_PACKED_MAXIMUM_WIDTH: u32 = 32;
pub const ACT_MAX_PACKED_MAXIMUM_MASK: u32 = 0xFFFFFFFF;
pub const ACT_CMD_OFFSET: usize = 0x0000001C;
pub const ACT_CMD_PACKED_TARGET_COMMAND_SHIFT: u32 = 0;
pub const ACT_CMD_PACKED_TARGET_COMMAND_WIDTH: u32 = 32;
pub const ACT_CMD_PACKED_TARGET_COMMAND_MASK: u32 = 0xFFFFFFFF;
pub const LAST_GOOD_OFFSET: usize = 0x00000020;
pub const LAST_GOOD_PACKED_LAST_ACCEPTED_COMMAND_SHIFT: u32 = 0;
pub const LAST_GOOD_PACKED_LAST_ACCEPTED_COMMAND_WIDTH: u32 = 32;
pub const LAST_GOOD_PACKED_LAST_ACCEPTED_COMMAND_MASK: u32 = 0xFFFFFFFF;
pub const TIMEOUT_CNT_OFFSET: usize = 0x00000024;
pub const TIMEOUT_CNT_CURRENT_TIMEOUT_AGE_SHIFT: u32 = 0;
pub const TIMEOUT_CNT_CURRENT_TIMEOUT_AGE_WIDTH: u32 = 32;
pub const TIMEOUT_CNT_CURRENT_TIMEOUT_AGE_MASK: u32 = 0xFFFFFFFF;
pub const FAULT_CAUSE_OFFSET: usize = 0x00000028;
pub const FAULT_CAUSE_STICKY_FAULT_BITS_SHIFT: u32 = 0;
pub const FAULT_CAUSE_STICKY_FAULT_BITS_WIDTH: u32 = 32;
pub const FAULT_CAUSE_STICKY_FAULT_BITS_MASK: u32 = 0xFFFFFFFF;
pub const IRQ_ACK_OFFSET: usize = 0x0000002C;
pub const IRQ_ACK_ACKNOWLEDGE_SHIFT: u32 = 0;
pub const IRQ_ACK_ACKNOWLEDGE_WIDTH: u32 = 1;
pub const IRQ_ACK_ACKNOWLEDGE_MASK: u32 = 0x00000001;
pub const IRQ_ACK_RESERVED_SHIFT: u32 = 1;
pub const IRQ_ACK_RESERVED_WIDTH: u32 = 31;
pub const IRQ_ACK_RESERVED_MASK: u32 = 0xFFFFFFFE;

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
pub fn get_control_clear_faults() -> u32 {
    (read_control() & CONTROL_CLEAR_FAULTS_MASK) >> CONTROL_CLEAR_FAULTS_SHIFT
}

#[inline]
pub fn set_control_clear_faults(value: u32) {
    let current = read_control();
    let next = (current & !CONTROL_CLEAR_FAULTS_MASK) | ((value << CONTROL_CLEAR_FAULTS_SHIFT) & CONTROL_CLEAR_FAULTS_MASK);
    write_control(next);
}

#[inline]
pub fn get_control_arm_safe_fallback() -> u32 {
    (read_control() & CONTROL_ARM_SAFE_FALLBACK_MASK) >> CONTROL_ARM_SAFE_FALLBACK_SHIFT
}

#[inline]
pub fn set_control_arm_safe_fallback(value: u32) {
    let current = read_control();
    let next = (current & !CONTROL_ARM_SAFE_FALLBACK_MASK) | ((value << CONTROL_ARM_SAFE_FALLBACK_SHIFT) & CONTROL_ARM_SAFE_FALLBACK_MASK);
    write_control(next);
}

#[inline]
pub fn get_control_bypass_output_hold() -> u32 {
    (read_control() & CONTROL_BYPASS_OUTPUT_HOLD_MASK) >> CONTROL_BYPASS_OUTPUT_HOLD_SHIFT
}

#[inline]
pub fn set_control_bypass_output_hold(value: u32) {
    let current = read_control();
    let next = (current & !CONTROL_BYPASS_OUTPUT_HOLD_MASK) | ((value << CONTROL_BYPASS_OUTPUT_HOLD_SHIFT) & CONTROL_BYPASS_OUTPUT_HOLD_MASK);
    write_control(next);
}

#[inline]
pub fn get_control_mode() -> u32 {
    (read_control() & CONTROL_MODE_MASK) >> CONTROL_MODE_SHIFT
}

#[inline]
pub fn set_control_mode(value: u32) {
    let current = read_control();
    let next = (current & !CONTROL_MODE_MASK) | ((value << CONTROL_MODE_SHIFT) & CONTROL_MODE_MASK);
    write_control(next);
}

#[inline]
pub fn get_control_reserved() -> u32 {
    (read_control() & CONTROL_RESERVED_MASK) >> CONTROL_RESERVED_SHIFT
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
pub fn get_status_command_accepted() -> u32 {
    (read_status() & STATUS_COMMAND_ACCEPTED_MASK) >> STATUS_COMMAND_ACCEPTED_SHIFT
}

#[inline]
pub fn get_status_stale_rejected() -> u32 {
    (read_status() & STATUS_STALE_REJECTED_MASK) >> STATUS_STALE_REJECTED_SHIFT
}

#[inline]
pub fn get_status_timeout_fault() -> u32 {
    (read_status() & STATUS_TIMEOUT_FAULT_MASK) >> STATUS_TIMEOUT_FAULT_SHIFT
}

#[inline]
pub fn get_status_invalid_input() -> u32 {
    (read_status() & STATUS_INVALID_INPUT_MASK) >> STATUS_INVALID_INPUT_SHIFT
}

#[inline]
pub fn get_status_clamp_applied() -> u32 {
    (read_status() & STATUS_CLAMP_APPLIED_MASK) >> STATUS_CLAMP_APPLIED_SHIFT
}

#[inline]
pub fn get_status_safe_fallback_active() -> u32 {
    (read_status() & STATUS_SAFE_FALLBACK_ACTIVE_MASK) >> STATUS_SAFE_FALLBACK_ACTIVE_SHIFT
}

#[inline]
pub fn get_status_irq_pending() -> u32 {
    (read_status() & STATUS_IRQ_PENDING_MASK) >> STATUS_IRQ_PENDING_SHIFT
}

#[inline]
pub fn get_status_reserved() -> u32 {
    (read_status() & STATUS_RESERVED_MASK) >> STATUS_RESERVED_SHIFT
}

#[inline]
pub fn read_seq_in() -> u32 {
    read_reg(SEQ_IN_OFFSET)
}

#[inline]
pub fn write_seq_in(value: u32) {
    write_reg(SEQ_IN_OFFSET, value)
}

#[inline]
pub fn get_seq_in_sequence_number() -> u32 {
    (read_seq_in() & SEQ_IN_SEQUENCE_NUMBER_MASK) >> SEQ_IN_SEQUENCE_NUMBER_SHIFT
}

#[inline]
pub fn set_seq_in_sequence_number(value: u32) {
    let current = read_seq_in();
    let next = (current & !SEQ_IN_SEQUENCE_NUMBER_MASK) | ((value << SEQ_IN_SEQUENCE_NUMBER_SHIFT) & SEQ_IN_SEQUENCE_NUMBER_MASK);
    write_seq_in(next);
}

#[inline]
pub fn read_age_limit() -> u32 {
    read_reg(AGE_LIMIT_OFFSET)
}

#[inline]
pub fn write_age_limit(value: u32) {
    write_reg(AGE_LIMIT_OFFSET, value)
}

#[inline]
pub fn get_age_limit_max_age_cycles() -> u32 {
    (read_age_limit() & AGE_LIMIT_MAX_AGE_CYCLES_MASK) >> AGE_LIMIT_MAX_AGE_CYCLES_SHIFT
}

#[inline]
pub fn set_age_limit_max_age_cycles(value: u32) {
    let current = read_age_limit();
    let next = (current & !AGE_LIMIT_MAX_AGE_CYCLES_MASK) | ((value << AGE_LIMIT_MAX_AGE_CYCLES_SHIFT) & AGE_LIMIT_MAX_AGE_CYCLES_MASK);
    write_age_limit(next);
}

#[inline]
pub fn read_velocity_mps() -> u32 {
    read_reg(VELOCITY_MPS_OFFSET)
}

#[inline]
pub fn write_velocity_mps(value: u32) {
    write_reg(VELOCITY_MPS_OFFSET, value)
}

#[inline]
pub fn get_velocity_mps_velocity_fixed_point() -> u32 {
    (read_velocity_mps() & VELOCITY_MPS_VELOCITY_FIXED_POINT_MASK) >> VELOCITY_MPS_VELOCITY_FIXED_POINT_SHIFT
}

#[inline]
pub fn set_velocity_mps_velocity_fixed_point(value: u32) {
    let current = read_velocity_mps();
    let next = (current & !VELOCITY_MPS_VELOCITY_FIXED_POINT_MASK) | ((value << VELOCITY_MPS_VELOCITY_FIXED_POINT_SHIFT) & VELOCITY_MPS_VELOCITY_FIXED_POINT_MASK);
    write_velocity_mps(next);
}

#[inline]
pub fn read_act_min() -> u32 {
    read_reg(ACT_MIN_OFFSET)
}

#[inline]
pub fn write_act_min(value: u32) {
    write_reg(ACT_MIN_OFFSET, value)
}

#[inline]
pub fn get_act_min_packed_minimum() -> u32 {
    (read_act_min() & ACT_MIN_PACKED_MINIMUM_MASK) >> ACT_MIN_PACKED_MINIMUM_SHIFT
}

#[inline]
pub fn set_act_min_packed_minimum(value: u32) {
    let current = read_act_min();
    let next = (current & !ACT_MIN_PACKED_MINIMUM_MASK) | ((value << ACT_MIN_PACKED_MINIMUM_SHIFT) & ACT_MIN_PACKED_MINIMUM_MASK);
    write_act_min(next);
}

#[inline]
pub fn read_act_max() -> u32 {
    read_reg(ACT_MAX_OFFSET)
}

#[inline]
pub fn write_act_max(value: u32) {
    write_reg(ACT_MAX_OFFSET, value)
}

#[inline]
pub fn get_act_max_packed_maximum() -> u32 {
    (read_act_max() & ACT_MAX_PACKED_MAXIMUM_MASK) >> ACT_MAX_PACKED_MAXIMUM_SHIFT
}

#[inline]
pub fn set_act_max_packed_maximum(value: u32) {
    let current = read_act_max();
    let next = (current & !ACT_MAX_PACKED_MAXIMUM_MASK) | ((value << ACT_MAX_PACKED_MAXIMUM_SHIFT) & ACT_MAX_PACKED_MAXIMUM_MASK);
    write_act_max(next);
}

#[inline]
pub fn read_act_cmd() -> u32 {
    read_reg(ACT_CMD_OFFSET)
}

#[inline]
pub fn write_act_cmd(value: u32) {
    write_reg(ACT_CMD_OFFSET, value)
}

#[inline]
pub fn get_act_cmd_packed_target_command() -> u32 {
    (read_act_cmd() & ACT_CMD_PACKED_TARGET_COMMAND_MASK) >> ACT_CMD_PACKED_TARGET_COMMAND_SHIFT
}

#[inline]
pub fn set_act_cmd_packed_target_command(value: u32) {
    let current = read_act_cmd();
    let next = (current & !ACT_CMD_PACKED_TARGET_COMMAND_MASK) | ((value << ACT_CMD_PACKED_TARGET_COMMAND_SHIFT) & ACT_CMD_PACKED_TARGET_COMMAND_MASK);
    write_act_cmd(next);
}

#[inline]
pub fn read_last_good() -> u32 {
    read_reg(LAST_GOOD_OFFSET)
}

#[inline]
pub fn get_last_good_packed_last_accepted_command() -> u32 {
    (read_last_good() & LAST_GOOD_PACKED_LAST_ACCEPTED_COMMAND_MASK) >> LAST_GOOD_PACKED_LAST_ACCEPTED_COMMAND_SHIFT
}

#[inline]
pub fn read_timeout_cnt() -> u32 {
    read_reg(TIMEOUT_CNT_OFFSET)
}

#[inline]
pub fn get_timeout_cnt_current_timeout_age() -> u32 {
    (read_timeout_cnt() & TIMEOUT_CNT_CURRENT_TIMEOUT_AGE_MASK) >> TIMEOUT_CNT_CURRENT_TIMEOUT_AGE_SHIFT
}

#[inline]
pub fn read_fault_cause() -> u32 {
    read_reg(FAULT_CAUSE_OFFSET)
}

#[inline]
pub fn get_fault_cause_sticky_fault_bits() -> u32 {
    (read_fault_cause() & FAULT_CAUSE_STICKY_FAULT_BITS_MASK) >> FAULT_CAUSE_STICKY_FAULT_BITS_SHIFT
}

#[inline]
pub fn read_irq_ack() -> u32 {
    read_reg(IRQ_ACK_OFFSET)
}

#[inline]
pub fn write_irq_ack(value: u32) {
    write_reg(IRQ_ACK_OFFSET, value)
}

#[inline]
pub fn get_irq_ack_acknowledge() -> u32 {
    (read_irq_ack() & IRQ_ACK_ACKNOWLEDGE_MASK) >> IRQ_ACK_ACKNOWLEDGE_SHIFT
}

#[inline]
pub fn set_irq_ack_acknowledge(value: u32) {
    let current = read_irq_ack();
    let next = (current & !IRQ_ACK_ACKNOWLEDGE_MASK) | ((value << IRQ_ACK_ACKNOWLEDGE_SHIFT) & IRQ_ACK_ACKNOWLEDGE_MASK);
    write_irq_ack(next);
}

#[inline]
pub fn get_irq_ack_reserved() -> u32 {
    (read_irq_ack() & IRQ_ACK_RESERVED_MASK) >> IRQ_ACK_RESERVED_SHIFT
}

#[inline]
pub fn set_irq_ack_reserved(value: u32) {
    let current = read_irq_ack();
    let next = (current & !IRQ_ACK_RESERVED_MASK) | ((value << IRQ_ACK_RESERVED_SHIFT) & IRQ_ACK_RESERVED_MASK);
    write_irq_ack(next);
}

