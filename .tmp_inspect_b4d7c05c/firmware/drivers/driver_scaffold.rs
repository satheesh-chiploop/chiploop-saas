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
    pub fn get_ctrl_start_request(&self) -> bool {
        get_ctrl_start_request() != 0
    }

    #[inline]
    pub fn set_ctrl_start_request(&self, value: bool) {
        set_ctrl_start_request(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_clear_faults(&self) -> bool {
        get_ctrl_clear_faults() != 0
    }

    #[inline]
    pub fn set_ctrl_clear_faults(&self, value: bool) {
        set_ctrl_clear_faults(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_safe_mode_select(&self) -> bool {
        get_ctrl_safe_mode_select() != 0
    }

    #[inline]
    pub fn set_ctrl_safe_mode_select(&self, value: bool) {
        set_ctrl_safe_mode_select(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn read_request(&self) -> u32 {
        read_request()
    }

    #[inline]
    pub fn write_request(&self, value: u32) {
        write_request(value)
    }

    #[inline]
    pub fn get_request_request_seq(&self) -> u16 {
        get_request_request_seq() as u16
    }

    #[inline]
    pub fn set_request_request_seq(&self, value: u16) {
        set_request_request_seq(value as u32)
    }

    #[inline]
    pub fn get_request_flow_condition_sel(&self) -> u8 {
        get_request_flow_condition_sel() as u8
    }

    #[inline]
    pub fn set_request_flow_condition_sel(&self, value: u8) {
        set_request_flow_condition_sel(value as u32)
    }

    #[inline]
    pub fn get_request_control_mode(&self) -> u8 {
        get_request_control_mode() as u8
    }

    #[inline]
    pub fn set_request_control_mode(&self, value: u8) {
        set_request_control_mode(value as u32)
    }

    #[inline]
    pub fn read_request_velocity(&self) -> u32 {
        read_request_velocity()
    }

    #[inline]
    pub fn write_request_velocity(&self, value: u32) {
        write_request_velocity(value)
    }

    #[inline]
    pub fn get_request_velocity_stream_velocity(&self) -> u32 {
        get_request_velocity_stream_velocity() as u32
    }

    #[inline]
    pub fn set_request_velocity_stream_velocity(&self, value: u32) {
        set_request_velocity_stream_velocity(value as u32)
    }

    #[inline]
    pub fn read_geometry(&self) -> u32 {
        read_geometry()
    }

    #[inline]
    pub fn write_geometry(&self, value: u32) {
        write_geometry(value)
    }

    #[inline]
    pub fn get_geometry_geometry_id(&self) -> u16 {
        get_geometry_geometry_id() as u16
    }

    #[inline]
    pub fn set_geometry_geometry_id(&self, value: u16) {
        set_geometry_geometry_id(value as u32)
    }

    #[inline]
    pub fn read_timeout_cycles(&self) -> u32 {
        read_timeout_cycles()
    }

    #[inline]
    pub fn write_timeout_cycles(&self, value: u32) {
        write_timeout_cycles(value)
    }

    #[inline]
    pub fn get_timeout_cycles_timeout_cycles(&self) -> u32 {
        get_timeout_cycles_timeout_cycles() as u32
    }

    #[inline]
    pub fn set_timeout_cycles_timeout_cycles(&self, value: u32) {
        set_timeout_cycles_timeout_cycles(value as u32)
    }

    #[inline]
    pub fn read_freshness_cycles(&self) -> u32 {
        read_freshness_cycles()
    }

    #[inline]
    pub fn write_freshness_cycles(&self, value: u32) {
        write_freshness_cycles(value)
    }

    #[inline]
    pub fn get_freshness_cycles_freshness_cycles(&self) -> u32 {
        get_freshness_cycles_freshness_cycles() as u32
    }

    #[inline]
    pub fn set_freshness_cycles_freshness_cycles(&self, value: u32) {
        set_freshness_cycles_freshness_cycles(value as u32)
    }

    #[inline]
    pub fn read_actuator_min(&self) -> u32 {
        read_actuator_min()
    }

    #[inline]
    pub fn write_actuator_min(&self, value: u32) {
        write_actuator_min(value)
    }

    #[inline]
    pub fn get_actuator_min_actuator_min(&self) -> u32 {
        get_actuator_min_actuator_min() as u32
    }

    #[inline]
    pub fn set_actuator_min_actuator_min(&self, value: u32) {
        set_actuator_min_actuator_min(value as u32)
    }

    #[inline]
    pub fn read_actuator_max(&self) -> u32 {
        read_actuator_max()
    }

    #[inline]
    pub fn write_actuator_max(&self, value: u32) {
        write_actuator_max(value)
    }

    #[inline]
    pub fn get_actuator_max_actuator_max(&self) -> u32 {
        get_actuator_max_actuator_max() as u32
    }

    #[inline]
    pub fn set_actuator_max_actuator_max(&self, value: u32) {
        set_actuator_max_actuator_max(value as u32)
    }

    #[inline]
    pub fn read_rate_limit(&self) -> u32 {
        read_rate_limit()
    }

    #[inline]
    pub fn write_rate_limit(&self, value: u32) {
        write_rate_limit(value)
    }

    #[inline]
    pub fn get_rate_limit_rate_limit(&self) -> u32 {
        get_rate_limit_rate_limit() as u32
    }

    #[inline]
    pub fn set_rate_limit_rate_limit(&self, value: u32) {
        set_rate_limit_rate_limit(value as u32)
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
    pub fn get_status_response_valid(&self) -> bool {
        get_status_response_valid() != 0
    }

    #[inline]
    pub fn get_status_timeout_fault(&self) -> bool {
        get_status_timeout_fault() != 0
    }

    #[inline]
    pub fn get_status_stale_fault(&self) -> bool {
        get_status_stale_fault() != 0
    }

    #[inline]
    pub fn get_status_response_seq_mismatch(&self) -> bool {
        get_status_response_seq_mismatch() != 0
    }

    #[inline]
    pub fn get_status_invalid_payload_fault(&self) -> bool {
        get_status_invalid_payload_fault() != 0
    }

    #[inline]
    pub fn get_status_fallback_active(&self) -> bool {
        get_status_fallback_active() != 0
    }

    #[inline]
    pub fn get_status_fault_pending(&self) -> bool {
        get_status_fault_pending() != 0
    }

    #[inline]
    pub fn read_sequence(&self) -> u32 {
        read_sequence()
    }

    #[inline]
    pub fn get_sequence_current_sequence(&self) -> u16 {
        get_sequence_current_sequence() as u16
    }

    #[inline]
    pub fn get_sequence_last_good_command(&self) -> u16 {
        get_sequence_last_good_command() as u16
    }

    #[inline]
    pub fn read_last_good_command(&self) -> u32 {
        read_last_good_command()
    }

    #[inline]
    pub fn get_last_good_command_last_good_command(&self) -> u32 {
        get_last_good_command_last_good_command() as u32
    }

}
