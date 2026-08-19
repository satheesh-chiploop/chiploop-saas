use crate::hal::registers::*;

pub struct DigitalSubsystemDriver;

impl DigitalSubsystemDriver {
    #[inline]
    pub const fn new() -> Self {
        Self
    }

    #[inline]
    pub fn read_control(&self) -> u32 {
        read_control()
    }

    #[inline]
    pub fn write_control(&self, value: u32) {
        write_control(value)
    }

    #[inline]
    pub fn get_control_enable(&self) -> bool {
        get_control_enable() != 0
    }

    #[inline]
    pub fn set_control_enable(&self, value: bool) {
        set_control_enable(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_control_clear_faults(&self) -> bool {
        get_control_clear_faults() != 0
    }

    #[inline]
    pub fn set_control_clear_faults(&self, value: bool) {
        set_control_clear_faults(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_control_arm_safe_fallback(&self) -> bool {
        get_control_arm_safe_fallback() != 0
    }

    #[inline]
    pub fn set_control_arm_safe_fallback(&self, value: bool) {
        set_control_arm_safe_fallback(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_control_bypass_output_hold(&self) -> bool {
        get_control_bypass_output_hold() != 0
    }

    #[inline]
    pub fn set_control_bypass_output_hold(&self, value: bool) {
        set_control_bypass_output_hold(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_control_mode(&self) -> u8 {
        get_control_mode() as u8
    }

    #[inline]
    pub fn set_control_mode(&self, value: u8) {
        set_control_mode(value as u32)
    }

    #[inline]
    pub fn get_control_reserved(&self) -> u32 {
        get_control_reserved() as u32
    }

    #[inline]
    pub fn read_status(&self) -> u32 {
        read_status()
    }

    #[inline]
    pub fn get_status_busy(&self) -> bool {
        get_status_busy() != 0
    }

    #[inline]
    pub fn get_status_command_accepted(&self) -> bool {
        get_status_command_accepted() != 0
    }

    #[inline]
    pub fn get_status_stale_rejected(&self) -> bool {
        get_status_stale_rejected() != 0
    }

    #[inline]
    pub fn get_status_timeout_fault(&self) -> bool {
        get_status_timeout_fault() != 0
    }

    #[inline]
    pub fn get_status_invalid_input(&self) -> bool {
        get_status_invalid_input() != 0
    }

    #[inline]
    pub fn get_status_clamp_applied(&self) -> bool {
        get_status_clamp_applied() != 0
    }

    #[inline]
    pub fn get_status_safe_fallback_active(&self) -> bool {
        get_status_safe_fallback_active() != 0
    }

    #[inline]
    pub fn get_status_irq_pending(&self) -> bool {
        get_status_irq_pending() != 0
    }

    #[inline]
    pub fn get_status_reserved(&self) -> u32 {
        get_status_reserved() as u32
    }

    #[inline]
    pub fn read_seq_in(&self) -> u32 {
        read_seq_in()
    }

    #[inline]
    pub fn write_seq_in(&self, value: u32) {
        write_seq_in(value)
    }

    #[inline]
    pub fn get_seq_in_sequence_number(&self) -> u32 {
        get_seq_in_sequence_number() as u32
    }

    #[inline]
    pub fn set_seq_in_sequence_number(&self, value: u32) {
        set_seq_in_sequence_number(value as u32)
    }

    #[inline]
    pub fn read_age_limit(&self) -> u32 {
        read_age_limit()
    }

    #[inline]
    pub fn write_age_limit(&self, value: u32) {
        write_age_limit(value)
    }

    #[inline]
    pub fn get_age_limit_max_age_cycles(&self) -> u32 {
        get_age_limit_max_age_cycles() as u32
    }

    #[inline]
    pub fn set_age_limit_max_age_cycles(&self, value: u32) {
        set_age_limit_max_age_cycles(value as u32)
    }

    #[inline]
    pub fn read_velocity_mps(&self) -> u32 {
        read_velocity_mps()
    }

    #[inline]
    pub fn write_velocity_mps(&self, value: u32) {
        write_velocity_mps(value)
    }

    #[inline]
    pub fn get_velocity_mps_velocity_fixed_point(&self) -> u32 {
        get_velocity_mps_velocity_fixed_point() as u32
    }

    #[inline]
    pub fn set_velocity_mps_velocity_fixed_point(&self, value: u32) {
        set_velocity_mps_velocity_fixed_point(value as u32)
    }

    #[inline]
    pub fn read_act_min(&self) -> u32 {
        read_act_min()
    }

    #[inline]
    pub fn write_act_min(&self, value: u32) {
        write_act_min(value)
    }

    #[inline]
    pub fn get_act_min_packed_minimum(&self) -> u32 {
        get_act_min_packed_minimum() as u32
    }

    #[inline]
    pub fn set_act_min_packed_minimum(&self, value: u32) {
        set_act_min_packed_minimum(value as u32)
    }

    #[inline]
    pub fn read_act_max(&self) -> u32 {
        read_act_max()
    }

    #[inline]
    pub fn write_act_max(&self, value: u32) {
        write_act_max(value)
    }

    #[inline]
    pub fn get_act_max_packed_maximum(&self) -> u32 {
        get_act_max_packed_maximum() as u32
    }

    #[inline]
    pub fn set_act_max_packed_maximum(&self, value: u32) {
        set_act_max_packed_maximum(value as u32)
    }

    #[inline]
    pub fn read_act_cmd(&self) -> u32 {
        read_act_cmd()
    }

    #[inline]
    pub fn write_act_cmd(&self, value: u32) {
        write_act_cmd(value)
    }

    #[inline]
    pub fn get_act_cmd_packed_target_command(&self) -> u32 {
        get_act_cmd_packed_target_command() as u32
    }

    #[inline]
    pub fn set_act_cmd_packed_target_command(&self, value: u32) {
        set_act_cmd_packed_target_command(value as u32)
    }

    #[inline]
    pub fn read_last_good(&self) -> u32 {
        read_last_good()
    }

    #[inline]
    pub fn get_last_good_packed_last_accepted_command(&self) -> u32 {
        get_last_good_packed_last_accepted_command() as u32
    }

    #[inline]
    pub fn read_timeout_cnt(&self) -> u32 {
        read_timeout_cnt()
    }

    #[inline]
    pub fn get_timeout_cnt_current_timeout_age(&self) -> u32 {
        get_timeout_cnt_current_timeout_age() as u32
    }

    #[inline]
    pub fn read_fault_cause(&self) -> u32 {
        read_fault_cause()
    }

    #[inline]
    pub fn get_fault_cause_sticky_fault_bits(&self) -> u32 {
        get_fault_cause_sticky_fault_bits() as u32
    }

    #[inline]
    pub fn read_irq_ack(&self) -> u32 {
        read_irq_ack()
    }

    #[inline]
    pub fn write_irq_ack(&self, value: u32) {
        write_irq_ack(value)
    }

    #[inline]
    pub fn get_irq_ack_acknowledge(&self) -> bool {
        get_irq_ack_acknowledge() != 0
    }

    #[inline]
    pub fn set_irq_ack_acknowledge(&self, value: bool) {
        set_irq_ack_acknowledge(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_irq_ack_reserved(&self) -> u32 {
        get_irq_ack_reserved() as u32
    }

    #[inline]
    pub fn set_irq_ack_reserved(&self, value: u32) {
        set_irq_ack_reserved(value as u32)
    }

}
