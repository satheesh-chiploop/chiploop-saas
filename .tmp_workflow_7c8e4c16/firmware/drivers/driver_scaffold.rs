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
    pub fn get_ctrl_enable(&self) -> bool {
        get_ctrl_enable() != 0
    }

    #[inline]
    pub fn set_ctrl_enable(&self, value: bool) {
        set_ctrl_enable(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_safe_fallback_select(&self) -> bool {
        get_ctrl_safe_fallback_select() != 0
    }

    #[inline]
    pub fn set_ctrl_safe_fallback_select(&self, value: bool) {
        set_ctrl_safe_fallback_select(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn read_max_cmd_pos(&self) -> u32 {
        read_max_cmd_pos()
    }

    #[inline]
    pub fn write_max_cmd_pos(&self, value: u32) {
        write_max_cmd_pos(value)
    }

    #[inline]
    pub fn get_max_cmd_pos_max_cmd_pos(&self) -> u32 {
        get_max_cmd_pos_max_cmd_pos() as u32
    }

    #[inline]
    pub fn set_max_cmd_pos_max_cmd_pos(&self, value: u32) {
        set_max_cmd_pos_max_cmd_pos(value as u32)
    }

    #[inline]
    pub fn read_min_cmd_pos(&self) -> u32 {
        read_min_cmd_pos()
    }

    #[inline]
    pub fn write_min_cmd_pos(&self, value: u32) {
        write_min_cmd_pos(value)
    }

    #[inline]
    pub fn get_min_cmd_pos_min_cmd_pos(&self) -> u32 {
        get_min_cmd_pos_min_cmd_pos() as u32
    }

    #[inline]
    pub fn set_min_cmd_pos_min_cmd_pos(&self, value: u32) {
        set_min_cmd_pos_min_cmd_pos(value as u32)
    }

    #[inline]
    pub fn read_max_cmd_rate(&self) -> u32 {
        read_max_cmd_rate()
    }

    #[inline]
    pub fn write_max_cmd_rate(&self, value: u32) {
        write_max_cmd_rate(value)
    }

    #[inline]
    pub fn get_max_cmd_rate_max_cmd_rate(&self) -> u32 {
        get_max_cmd_rate_max_cmd_rate() as u32
    }

    #[inline]
    pub fn set_max_cmd_rate_max_cmd_rate(&self, value: u32) {
        set_max_cmd_rate_max_cmd_rate(value as u32)
    }

    #[inline]
    pub fn read_stale_timeout_cycles(&self) -> u32 {
        read_stale_timeout_cycles()
    }

    #[inline]
    pub fn write_stale_timeout_cycles(&self, value: u32) {
        write_stale_timeout_cycles(value)
    }

    #[inline]
    pub fn get_stale_timeout_cycles_stale_timeout_cycles(&self) -> u32 {
        get_stale_timeout_cycles_stale_timeout_cycles() as u32
    }

    #[inline]
    pub fn set_stale_timeout_cycles_stale_timeout_cycles(&self, value: u32) {
        set_stale_timeout_cycles_stale_timeout_cycles(value as u32)
    }

    #[inline]
    pub fn read_response_timeout_cycles(&self) -> u32 {
        read_response_timeout_cycles()
    }

    #[inline]
    pub fn write_response_timeout_cycles(&self, value: u32) {
        write_response_timeout_cycles(value)
    }

    #[inline]
    pub fn get_response_timeout_cycles_response_timeout_cycles(&self) -> u32 {
        get_response_timeout_cycles_response_timeout_cycles() as u32
    }

    #[inline]
    pub fn set_response_timeout_cycles_response_timeout_cycles(&self, value: u32) {
        set_response_timeout_cycles_response_timeout_cycles(value as u32)
    }

    #[inline]
    pub fn read_sequence_expected(&self) -> u32 {
        read_sequence_expected()
    }

    #[inline]
    pub fn write_sequence_expected(&self, value: u32) {
        write_sequence_expected(value)
    }

    #[inline]
    pub fn get_sequence_expected_sequence_expected(&self) -> u32 {
        get_sequence_expected_sequence_expected() as u32
    }

    #[inline]
    pub fn set_sequence_expected_sequence_expected(&self, value: u32) {
        set_sequence_expected_sequence_expected(value as u32)
    }

    #[inline]
    pub fn read_stream_velocity_setpoint(&self) -> u32 {
        read_stream_velocity_setpoint()
    }

    #[inline]
    pub fn write_stream_velocity_setpoint(&self, value: u32) {
        write_stream_velocity_setpoint(value)
    }

    #[inline]
    pub fn get_stream_velocity_setpoint_stream_velocity_setpoint(&self) -> u32 {
        get_stream_velocity_setpoint_stream_velocity_setpoint() as u32
    }

    #[inline]
    pub fn set_stream_velocity_setpoint_stream_velocity_setpoint(&self, value: u32) {
        set_stream_velocity_setpoint_stream_velocity_setpoint(value as u32)
    }

    #[inline]
    pub fn read_fault_mask(&self) -> u32 {
        read_fault_mask()
    }

    #[inline]
    pub fn write_fault_mask(&self, value: u32) {
        write_fault_mask(value)
    }

    #[inline]
    pub fn get_fault_mask_fault_mask(&self) -> u32 {
        get_fault_mask_fault_mask() as u32
    }

    #[inline]
    pub fn set_fault_mask_fault_mask(&self, value: u32) {
        set_fault_mask_fault_mask(value as u32)
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
    pub fn get_status_accepted(&self) -> bool {
        get_status_accepted() != 0
    }

    #[inline]
    pub fn get_status_rejected_stale(&self) -> bool {
        get_status_rejected_stale() != 0
    }

    #[inline]
    pub fn get_status_rejected_seq(&self) -> bool {
        get_status_rejected_seq() != 0
    }

    #[inline]
    pub fn get_status_timeout(&self) -> bool {
        get_status_timeout() != 0
    }

    #[inline]
    pub fn get_status_fallback_active(&self) -> bool {
        get_status_fallback_active() != 0
    }

    #[inline]
    pub fn get_status_clamped(&self) -> bool {
        get_status_clamped() != 0
    }

    #[inline]
    pub fn get_status_fault_summary(&self) -> bool {
        get_status_fault_summary() != 0
    }

}
