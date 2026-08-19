use crate::hal::registers::*;

pub struct DigitalSubsystemDriver;

impl DigitalSubsystemDriver {
    #[inline]
    pub const fn new() -> Self {
        Self
    }

    #[inline]
    pub fn read_ctrl(&self) -> u32 {
        read_ctrl()
    }

    #[inline]
    pub fn write_ctrl(&self, value: u32) {
        write_ctrl(value)
    }

    #[inline]
    pub fn get_ctrl_mode(&self) -> u8 {
        get_ctrl_mode() as u8
    }

    #[inline]
    pub fn set_ctrl_mode(&self, value: u8) {
        set_ctrl_mode(value as u32)
    }

    #[inline]
    pub fn get_ctrl_cmd_valid(&self) -> bool {
        get_ctrl_cmd_valid() != 0
    }

    #[inline]
    pub fn set_ctrl_cmd_valid(&self, value: bool) {
        set_ctrl_cmd_valid(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_hold_last_safe(&self) -> bool {
        get_ctrl_hold_last_safe() != 0
    }

    #[inline]
    pub fn set_ctrl_hold_last_safe(&self, value: bool) {
        set_ctrl_hold_last_safe(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_fault_clear(&self) -> bool {
        get_ctrl_fault_clear() != 0
    }

    #[inline]
    pub fn set_ctrl_fault_clear(&self, value: bool) {
        set_ctrl_fault_clear(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_irq_ack(&self) -> bool {
        get_ctrl_irq_ack() != 0
    }

    #[inline]
    pub fn set_ctrl_irq_ack(&self, value: bool) {
        set_ctrl_irq_ack(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_irq_enable(&self) -> u8 {
        get_ctrl_irq_enable() as u8
    }

    #[inline]
    pub fn set_ctrl_irq_enable(&self, value: u8) {
        set_ctrl_irq_enable(value as u32)
    }

    #[inline]
    pub fn read_velocity_q8_8(&self) -> u32 {
        read_velocity_q8_8()
    }

    #[inline]
    pub fn write_velocity_q8_8(&self, value: u32) {
        write_velocity_q8_8(value)
    }

    #[inline]
    pub fn get_velocity_q8_8_velocity_q8_8(&self) -> u16 {
        get_velocity_q8_8_velocity_q8_8() as u16
    }

    #[inline]
    pub fn set_velocity_q8_8_velocity_q8_8(&self, value: u16) {
        set_velocity_q8_8_velocity_q8_8(value as u32)
    }

    #[inline]
    pub fn read_geometry_handle(&self) -> u32 {
        read_geometry_handle()
    }

    #[inline]
    pub fn write_geometry_handle(&self, value: u32) {
        write_geometry_handle(value)
    }

    #[inline]
    pub fn get_geometry_handle_geometry_handle(&self) -> u16 {
        get_geometry_handle_geometry_handle() as u16
    }

    #[inline]
    pub fn set_geometry_handle_geometry_handle(&self, value: u16) {
        set_geometry_handle_geometry_handle(value as u32)
    }

    #[inline]
    pub fn read_seq_ctrl(&self) -> u32 {
        read_seq_ctrl()
    }

    #[inline]
    pub fn write_seq_ctrl(&self, value: u32) {
        write_seq_ctrl(value)
    }

    #[inline]
    pub fn get_seq_ctrl_request_seq(&self) -> u16 {
        get_seq_ctrl_request_seq() as u16
    }

    #[inline]
    pub fn set_seq_ctrl_request_seq(&self, value: u16) {
        set_seq_ctrl_request_seq(value as u32)
    }

    #[inline]
    pub fn get_seq_ctrl_last_accepted_seq_ro(&self) -> u16 {
        get_seq_ctrl_last_accepted_seq_ro() as u16
    }

    #[inline]
    pub fn read_timeout_and_envelope(&self) -> u32 {
        read_timeout_and_envelope()
    }

    #[inline]
    pub fn write_timeout_and_envelope(&self, value: u32) {
        write_timeout_and_envelope(value)
    }

    #[inline]
    pub fn get_timeout_and_envelope_timeout_threshold(&self) -> u16 {
        get_timeout_and_envelope_timeout_threshold() as u16
    }

    #[inline]
    pub fn set_timeout_and_envelope_timeout_threshold(&self, value: u16) {
        set_timeout_and_envelope_timeout_threshold(value as u32)
    }

    #[inline]
    pub fn get_timeout_and_envelope_velocity_low_limit(&self) -> u8 {
        get_timeout_and_envelope_velocity_low_limit() as u8
    }

    #[inline]
    pub fn set_timeout_and_envelope_velocity_low_limit(&self, value: u8) {
        set_timeout_and_envelope_velocity_low_limit(value as u32)
    }

    #[inline]
    pub fn get_timeout_and_envelope_velocity_high_limit(&self) -> u8 {
        get_timeout_and_envelope_velocity_high_limit() as u8
    }

    #[inline]
    pub fn set_timeout_and_envelope_velocity_high_limit(&self, value: u8) {
        set_timeout_and_envelope_velocity_high_limit(value as u32)
    }

    #[inline]
    pub fn read_actuator_limits(&self) -> u32 {
        read_actuator_limits()
    }

    #[inline]
    pub fn write_actuator_limits(&self, value: u32) {
        write_actuator_limits(value)
    }

    #[inline]
    pub fn get_actuator_limits_actuator_min(&self) -> u16 {
        get_actuator_limits_actuator_min() as u16
    }

    #[inline]
    pub fn set_actuator_limits_actuator_min(&self, value: u16) {
        set_actuator_limits_actuator_min(value as u32)
    }

    #[inline]
    pub fn get_actuator_limits_actuator_max(&self) -> u16 {
        get_actuator_limits_actuator_max() as u16
    }

    #[inline]
    pub fn set_actuator_limits_actuator_max(&self, value: u16) {
        set_actuator_limits_actuator_max(value as u32)
    }

    #[inline]
    pub fn read_actuator_slew(&self) -> u32 {
        read_actuator_slew()
    }

    #[inline]
    pub fn write_actuator_slew(&self, value: u32) {
        write_actuator_slew(value)
    }

    #[inline]
    pub fn get_actuator_slew_actuator_slew(&self) -> u16 {
        get_actuator_slew_actuator_slew() as u16
    }

    #[inline]
    pub fn set_actuator_slew_actuator_slew(&self, value: u16) {
        set_actuator_slew_actuator_slew(value as u32)
    }

    #[inline]
    pub fn read_safe_state(&self) -> u32 {
        read_safe_state()
    }

    #[inline]
    pub fn write_safe_state(&self, value: u32) {
        write_safe_state(value)
    }

    #[inline]
    pub fn get_safe_state_safe_state_cmd(&self) -> u16 {
        get_safe_state_safe_state_cmd() as u16
    }

    #[inline]
    pub fn set_safe_state_safe_state_cmd(&self, value: u16) {
        set_safe_state_safe_state_cmd(value as u32)
    }

    #[inline]
    pub fn read_status0(&self) -> u32 {
        read_status0()
    }

    #[inline]
    pub fn get_status0_outstanding_req(&self) -> bool {
        get_status0_outstanding_req() != 0
    }

    #[inline]
    pub fn get_status0_status_safe_state(&self) -> bool {
        get_status0_status_safe_state() != 0
    }

    #[inline]
    pub fn get_status0_status_fault_latched(&self) -> bool {
        get_status0_status_fault_latched() != 0
    }

    #[inline]
    pub fn get_status0_status_actuator_valid(&self) -> bool {
        get_status0_status_actuator_valid() != 0
    }

    #[inline]
    pub fn get_status0_status_fault_code(&self) -> u8 {
        get_status0_status_fault_code() as u8
    }

    #[inline]
    pub fn read_status1(&self) -> u32 {
        read_status1()
    }

    #[inline]
    pub fn get_status1_status_timeout_count(&self) -> u16 {
        get_status1_status_timeout_count() as u16
    }

    #[inline]
    pub fn get_status1_status_stale_reject_count(&self) -> u16 {
        get_status1_status_stale_reject_count() as u16
    }

    #[inline]
    pub fn read_status2(&self) -> u32 {
        read_status2()
    }

    #[inline]
    pub fn get_status2_status_invalid_env_count(&self) -> u16 {
        get_status2_status_invalid_env_count() as u16
    }

    #[inline]
    pub fn get_status2_status_age_counter(&self) -> u16 {
        get_status2_status_age_counter() as u16
    }

    #[inline]
    pub fn read_status3(&self) -> u32 {
        read_status3()
    }

    #[inline]
    pub fn get_status3_status_last_accepted_seq(&self) -> u16 {
        get_status3_status_last_accepted_seq() as u16
    }

    #[inline]
    pub fn get_status3_status_response_seq(&self) -> u16 {
        get_status3_status_response_seq() as u16
    }

    #[inline]
    pub fn read_status4(&self) -> u32 {
        read_status4()
    }

    #[inline]
    pub fn get_status4_status_last_req_word_lo(&self) -> u32 {
        get_status4_status_last_req_word_lo() as u32
    }

    #[inline]
    pub fn read_status5(&self) -> u32 {
        read_status5()
    }

    #[inline]
    pub fn get_status5_status_last_req_word_hi(&self) -> u32 {
        get_status5_status_last_req_word_hi() as u32
    }

    #[inline]
    pub fn read_status6(&self) -> u32 {
        read_status6()
    }

    #[inline]
    pub fn get_status6_status_last_resp_word_lo(&self) -> u32 {
        get_status6_status_last_resp_word_lo() as u32
    }

    #[inline]
    pub fn read_status7(&self) -> u32 {
        read_status7()
    }

    #[inline]
    pub fn get_status7_status_last_resp_word_hi(&self) -> u32 {
        get_status7_status_last_resp_word_hi() as u32
    }

    #[inline]
    pub fn read_irq_status(&self) -> u32 {
        read_irq_status()
    }

    #[inline]
    pub fn write_irq_status(&self, value: u32) {
        write_irq_status(value)
    }

    #[inline]
    pub fn get_irq_status_resp_ready_sticky(&self) -> bool {
        get_irq_status_resp_ready_sticky() != 0
    }

    #[inline]
    pub fn set_irq_status_resp_ready_sticky(&self, value: bool) {
        set_irq_status_resp_ready_sticky(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_irq_status_timeout_sticky(&self) -> bool {
        get_irq_status_timeout_sticky() != 0
    }

    #[inline]
    pub fn set_irq_status_timeout_sticky(&self, value: bool) {
        set_irq_status_timeout_sticky(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_irq_status_stale_reject_sticky(&self) -> bool {
        get_irq_status_stale_reject_sticky() != 0
    }

    #[inline]
    pub fn set_irq_status_stale_reject_sticky(&self, value: bool) {
        set_irq_status_stale_reject_sticky(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_irq_status_invalid_env_sticky(&self) -> bool {
        get_irq_status_invalid_env_sticky() != 0
    }

    #[inline]
    pub fn set_irq_status_invalid_env_sticky(&self, value: bool) {
        set_irq_status_invalid_env_sticky(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_irq_status_fault_clear_event(&self) -> bool {
        get_irq_status_fault_clear_event() != 0
    }

    #[inline]
    pub fn set_irq_status_fault_clear_event(&self, value: bool) {
        set_irq_status_fault_clear_event(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn read_fault_status(&self) -> u32 {
        read_fault_status()
    }

    #[inline]
    pub fn get_fault_status_fault_code(&self) -> u8 {
        get_fault_status_fault_code() as u8
    }

    #[inline]
    pub fn get_fault_status_fault_latched(&self) -> bool {
        get_fault_status_fault_latched() != 0
    }

    #[inline]
    pub fn get_fault_status_safe_state(&self) -> bool {
        get_fault_status_safe_state() != 0
    }

}
