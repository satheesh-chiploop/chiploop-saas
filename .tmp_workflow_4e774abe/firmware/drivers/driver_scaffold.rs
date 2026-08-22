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
    pub fn get_ctrl_command_valid(&self) -> bool {
        get_ctrl_command_valid() != 0
    }

    #[inline]
    pub fn set_ctrl_command_valid(&self, value: bool) {
        set_ctrl_command_valid(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_control_mode(&self) -> u8 {
        get_ctrl_control_mode() as u8
    }

    #[inline]
    pub fn set_ctrl_control_mode(&self, value: u8) {
        set_ctrl_control_mode(value as u32)
    }

    #[inline]
    pub fn get_ctrl_integrity(&self) -> u8 {
        get_ctrl_integrity() as u8
    }

    #[inline]
    pub fn set_ctrl_integrity(&self, value: u8) {
        set_ctrl_integrity(value as u32)
    }

    #[inline]
    pub fn read_cmd_id_seq(&self) -> u32 {
        read_cmd_id_seq()
    }

    #[inline]
    pub fn write_cmd_id_seq(&self, value: u32) {
        write_cmd_id_seq(value)
    }

    #[inline]
    pub fn get_cmd_id_seq_command_id(&self) -> u8 {
        get_cmd_id_seq_command_id() as u8
    }

    #[inline]
    pub fn set_cmd_id_seq_command_id(&self, value: u8) {
        set_cmd_id_seq_command_id(value as u32)
    }

    #[inline]
    pub fn get_cmd_id_seq_sequence_number(&self) -> u16 {
        get_cmd_id_seq_sequence_number() as u16
    }

    #[inline]
    pub fn set_cmd_id_seq_sequence_number(&self, value: u16) {
        set_cmd_id_seq_sequence_number(value as u32)
    }

    #[inline]
    pub fn get_cmd_id_seq_age_or_timestamp(&self) -> u8 {
        get_cmd_id_seq_age_or_timestamp() as u8
    }

    #[inline]
    pub fn set_cmd_id_seq_age_or_timestamp(&self, value: u8) {
        set_cmd_id_seq_age_or_timestamp(value as u32)
    }

    #[inline]
    pub fn read_cmd_pos(&self) -> u32 {
        read_cmd_pos()
    }

    #[inline]
    pub fn write_cmd_pos(&self, value: u32) {
        write_cmd_pos(value)
    }

    #[inline]
    pub fn get_cmd_pos_requested_actuator_position(&self) -> u8 {
        get_cmd_pos_requested_actuator_position() as u8
    }

    #[inline]
    pub fn set_cmd_pos_requested_actuator_position(&self, value: u8) {
        set_cmd_pos_requested_actuator_position(value as u32)
    }

    #[inline]
    pub fn read_cfg_timeout(&self) -> u32 {
        read_cfg_timeout()
    }

    #[inline]
    pub fn write_cfg_timeout(&self, value: u32) {
        write_cfg_timeout(value)
    }

    #[inline]
    pub fn get_cfg_timeout_timeout_limit(&self) -> u16 {
        get_cfg_timeout_timeout_limit() as u16
    }

    #[inline]
    pub fn set_cfg_timeout_timeout_limit(&self, value: u16) {
        set_cfg_timeout_timeout_limit(value as u32)
    }

    #[inline]
    pub fn get_cfg_timeout_seq_policy(&self) -> u8 {
        get_cfg_timeout_seq_policy() as u8
    }

    #[inline]
    pub fn set_cfg_timeout_seq_policy(&self, value: u8) {
        set_cfg_timeout_seq_policy(value as u32)
    }

    #[inline]
    pub fn get_cfg_timeout_control_mode_permit(&self) -> u8 {
        get_cfg_timeout_control_mode_permit() as u8
    }

    #[inline]
    pub fn set_cfg_timeout_control_mode_permit(&self, value: u8) {
        set_cfg_timeout_control_mode_permit(value as u32)
    }

    #[inline]
    pub fn read_cfg_limits(&self) -> u32 {
        read_cfg_limits()
    }

    #[inline]
    pub fn write_cfg_limits(&self, value: u32) {
        write_cfg_limits(value)
    }

    #[inline]
    pub fn get_cfg_limits_act_min(&self) -> u8 {
        get_cfg_limits_act_min() as u8
    }

    #[inline]
    pub fn set_cfg_limits_act_min(&self, value: u8) {
        set_cfg_limits_act_min(value as u32)
    }

    #[inline]
    pub fn get_cfg_limits_act_max(&self) -> u8 {
        get_cfg_limits_act_max() as u8
    }

    #[inline]
    pub fn set_cfg_limits_act_max(&self, value: u8) {
        set_cfg_limits_act_max(value as u32)
    }

    #[inline]
    pub fn get_cfg_limits_safe_min(&self) -> u8 {
        get_cfg_limits_safe_min() as u8
    }

    #[inline]
    pub fn set_cfg_limits_safe_min(&self, value: u8) {
        set_cfg_limits_safe_min(value as u32)
    }

    #[inline]
    pub fn get_cfg_limits_safe_max(&self) -> u8 {
        get_cfg_limits_safe_max() as u8
    }

    #[inline]
    pub fn set_cfg_limits_safe_max(&self, value: u8) {
        set_cfg_limits_safe_max(value as u32)
    }

    #[inline]
    pub fn read_irq_ctrl(&self) -> u32 {
        read_irq_ctrl()
    }

    #[inline]
    pub fn write_irq_ctrl(&self, value: u32) {
        write_irq_ctrl(value)
    }

    #[inline]
    pub fn get_irq_ctrl_irq_enable(&self) -> u8 {
        get_irq_ctrl_irq_enable() as u8
    }

    #[inline]
    pub fn set_irq_ctrl_irq_enable(&self, value: u8) {
        set_irq_ctrl_irq_enable(value as u32)
    }

    #[inline]
    pub fn get_irq_ctrl_clear_sticky_faults(&self) -> bool {
        get_irq_ctrl_clear_sticky_faults() != 0
    }

    #[inline]
    pub fn set_irq_ctrl_clear_sticky_faults(&self, value: bool) {
        set_irq_ctrl_clear_sticky_faults(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn read_status(&self) -> u32 {
        read_status()
    }

    #[inline]
    pub fn get_status_accepted_event(&self) -> bool {
        get_status_accepted_event() != 0
    }

    #[inline]
    pub fn get_status_rejected_event(&self) -> bool {
        get_status_rejected_event() != 0
    }

    #[inline]
    pub fn get_status_stale_data_fault(&self) -> bool {
        get_status_stale_data_fault() != 0
    }

    #[inline]
    pub fn get_status_timeout_fault(&self) -> bool {
        get_status_timeout_fault() != 0
    }

    #[inline]
    pub fn get_status_clamp_applied(&self) -> bool {
        get_status_clamp_applied() != 0
    }

    #[inline]
    pub fn get_status_fallback_active(&self) -> bool {
        get_status_fallback_active() != 0
    }

    #[inline]
    pub fn get_status_sequence_number_seen(&self) -> u16 {
        get_status_sequence_number_seen() as u16
    }

    #[inline]
    pub fn get_status_last_fault_code(&self) -> u8 {
        get_status_last_fault_code() as u8
    }

    #[inline]
    pub fn read_watchdog(&self) -> u32 {
        read_watchdog()
    }

    #[inline]
    pub fn get_watchdog_watchdog_count(&self) -> u16 {
        get_watchdog_watchdog_count() as u16
    }

    #[inline]
    pub fn get_watchdog_status_capture_valid(&self) -> bool {
        get_watchdog_status_capture_valid() != 0
    }

}
