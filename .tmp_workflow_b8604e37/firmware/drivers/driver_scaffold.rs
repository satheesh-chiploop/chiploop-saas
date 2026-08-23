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
    pub fn get_ctrl_mode_sel(&self) -> u8 {
        get_ctrl_mode_sel() as u8
    }

    #[inline]
    pub fn set_ctrl_mode_sel(&self, value: u8) {
        set_ctrl_mode_sel(value as u32)
    }

    #[inline]
    pub fn get_ctrl_reserved_error_en(&self) -> bool {
        get_ctrl_reserved_error_en() != 0
    }

    #[inline]
    pub fn set_ctrl_reserved_error_en(&self, value: bool) {
        set_ctrl_reserved_error_en(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn read_reserved(&self) -> u32 {
        read_reserved()
    }

    #[inline]
    pub fn write_reserved(&self, value: u32) {
        write_reserved(value)
    }

    #[inline]
    pub fn get_reserved_reserved_error_flag(&self) -> bool {
        get_reserved_reserved_error_flag() != 0
    }

    #[inline]
    pub fn set_reserved_reserved_error_flag(&self, value: bool) {
        set_reserved_reserved_error_flag(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn read_env_limit(&self) -> u32 {
        read_env_limit()
    }

    #[inline]
    pub fn write_env_limit(&self, value: u32) {
        write_env_limit(value)
    }

    #[inline]
    pub fn get_env_limit_env_limit(&self) -> u16 {
        get_env_limit_env_limit() as u16
    }

    #[inline]
    pub fn set_env_limit_env_limit(&self, value: u16) {
        set_env_limit_env_limit(value as u32)
    }

    #[inline]
    pub fn read_stale_timeout(&self) -> u32 {
        read_stale_timeout()
    }

    #[inline]
    pub fn write_stale_timeout(&self, value: u32) {
        write_stale_timeout(value)
    }

    #[inline]
    pub fn get_stale_timeout_stale_timeout(&self) -> u16 {
        get_stale_timeout_stale_timeout() as u16
    }

    #[inline]
    pub fn set_stale_timeout_stale_timeout(&self, value: u16) {
        set_stale_timeout_stale_timeout(value as u32)
    }

    #[inline]
    pub fn read_seq_base(&self) -> u32 {
        read_seq_base()
    }

    #[inline]
    pub fn write_seq_base(&self, value: u32) {
        write_seq_base(value)
    }

    #[inline]
    pub fn get_seq_base_seq_base(&self) -> u16 {
        get_seq_base_seq_base() as u16
    }

    #[inline]
    pub fn set_seq_base_seq_base(&self, value: u16) {
        set_seq_base_seq_base(value as u32)
    }

    #[inline]
    pub fn read_heartbeat_timeout(&self) -> u32 {
        read_heartbeat_timeout()
    }

    #[inline]
    pub fn write_heartbeat_timeout(&self, value: u32) {
        write_heartbeat_timeout(value)
    }

    #[inline]
    pub fn get_heartbeat_timeout_heartbeat_timeout(&self) -> u16 {
        get_heartbeat_timeout_heartbeat_timeout() as u16
    }

    #[inline]
    pub fn set_heartbeat_timeout_heartbeat_timeout(&self, value: u16) {
        set_heartbeat_timeout_heartbeat_timeout(value as u32)
    }

    #[inline]
    pub fn read_act_clamp_min(&self) -> u32 {
        read_act_clamp_min()
    }

    #[inline]
    pub fn write_act_clamp_min(&self, value: u32) {
        write_act_clamp_min(value)
    }

    #[inline]
    pub fn get_act_clamp_min_act_min(&self) -> u16 {
        get_act_clamp_min_act_min() as u16
    }

    #[inline]
    pub fn set_act_clamp_min_act_min(&self, value: u16) {
        set_act_clamp_min_act_min(value as u32)
    }

    #[inline]
    pub fn read_act_clamp_max(&self) -> u32 {
        read_act_clamp_max()
    }

    #[inline]
    pub fn write_act_clamp_max(&self, value: u32) {
        write_act_clamp_max(value)
    }

    #[inline]
    pub fn get_act_clamp_max_act_max(&self) -> u16 {
        get_act_clamp_max_act_max() as u16
    }

    #[inline]
    pub fn set_act_clamp_max_act_max(&self, value: u16) {
        set_act_clamp_max_act_max(value as u32)
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
    pub fn get_rate_limit_rate_limit(&self) -> u8 {
        get_rate_limit_rate_limit() as u8
    }

    #[inline]
    pub fn set_rate_limit_rate_limit(&self, value: u8) {
        set_rate_limit_rate_limit(value as u32)
    }

    #[inline]
    pub fn read_safe_output(&self) -> u32 {
        read_safe_output()
    }

    #[inline]
    pub fn write_safe_output(&self, value: u32) {
        write_safe_output(value)
    }

    #[inline]
    pub fn get_safe_output_safe_output(&self) -> u16 {
        get_safe_output_safe_output() as u16
    }

    #[inline]
    pub fn set_safe_output_safe_output(&self, value: u16) {
        set_safe_output_safe_output(value as u32)
    }

    #[inline]
    pub fn read_fault_ctrl(&self) -> u32 {
        read_fault_ctrl()
    }

    #[inline]
    pub fn write_fault_ctrl(&self, value: u32) {
        write_fault_ctrl(value)
    }

    #[inline]
    pub fn get_fault_ctrl_fault_clear(&self) -> bool {
        get_fault_ctrl_fault_clear() != 0
    }

    #[inline]
    pub fn set_fault_ctrl_fault_clear(&self, value: bool) {
        set_fault_ctrl_fault_clear(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn read_status(&self) -> u32 {
        read_status()
    }

    #[inline]
    pub fn get_status_mode(&self) -> u8 {
        get_status_mode() as u8
    }

    #[inline]
    pub fn get_status_fault_latched(&self) -> bool {
        get_status_fault_latched() != 0
    }

    #[inline]
    pub fn get_status_timeout_status(&self) -> bool {
        get_status_timeout_status() != 0
    }

    #[inline]
    pub fn get_status_stale_status(&self) -> bool {
        get_status_stale_status() != 0
    }

    #[inline]
    pub fn get_status_heartbeat_seen(&self) -> bool {
        get_status_heartbeat_seen() != 0
    }

    #[inline]
    pub fn read_last_cmd(&self) -> u32 {
        read_last_cmd()
    }

    #[inline]
    pub fn get_last_cmd_last_cmd(&self) -> u16 {
        get_last_cmd_last_cmd() as u16
    }

    #[inline]
    pub fn read_last_seq(&self) -> u32 {
        read_last_seq()
    }

    #[inline]
    pub fn get_last_seq_last_seq(&self) -> u16 {
        get_last_seq_last_seq() as u16
    }

    #[inline]
    pub fn read_telem_accepted(&self) -> u32 {
        read_telem_accepted()
    }

    #[inline]
    pub fn get_telem_accepted_accepted_packets(&self) -> u16 {
        get_telem_accepted_accepted_packets() as u16
    }

    #[inline]
    pub fn read_telem_rejected(&self) -> u32 {
        read_telem_rejected()
    }

    #[inline]
    pub fn get_telem_rejected_rejected_packets(&self) -> u16 {
        get_telem_rejected_rejected_packets() as u16
    }

    #[inline]
    pub fn read_telem_timeout(&self) -> u32 {
        read_telem_timeout()
    }

    #[inline]
    pub fn get_telem_timeout_timeout_events(&self) -> u16 {
        get_telem_timeout_timeout_events() as u16
    }

    #[inline]
    pub fn read_telem_stale(&self) -> u32 {
        read_telem_stale()
    }

    #[inline]
    pub fn get_telem_stale_stale_events(&self) -> u16 {
        get_telem_stale_stale_events() as u16
    }

    #[inline]
    pub fn read_telem_fallback(&self) -> u32 {
        read_telem_fallback()
    }

    #[inline]
    pub fn get_telem_fallback_fallback_entries(&self) -> u16 {
        get_telem_fallback_fallback_entries() as u16
    }

    #[inline]
    pub fn read_telem_last_valid_seq(&self) -> u32 {
        read_telem_last_valid_seq()
    }

    #[inline]
    pub fn get_telem_last_valid_seq_last_valid_seq(&self) -> u16 {
        get_telem_last_valid_seq_last_valid_seq() as u16
    }

}
