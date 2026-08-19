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
    pub fn get_ctrl_clear_fault(&self) -> bool {
        get_ctrl_clear_fault() != 0
    }

    #[inline]
    pub fn set_ctrl_clear_fault(&self, value: bool) {
        set_ctrl_clear_fault(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_arm_output(&self) -> bool {
        get_ctrl_arm_output() != 0
    }

    #[inline]
    pub fn set_ctrl_arm_output(&self, value: bool) {
        set_ctrl_arm_output(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_request_start(&self) -> bool {
        get_ctrl_request_start() != 0
    }

    #[inline]
    pub fn set_ctrl_request_start(&self, value: bool) {
        set_ctrl_request_start(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_bypass_model(&self) -> bool {
        get_ctrl_bypass_model() != 0
    }

    #[inline]
    pub fn set_ctrl_bypass_model(&self, value: bool) {
        set_ctrl_bypass_model(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_reserved(&self) -> u32 {
        get_ctrl_reserved() as u32
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
    pub fn get_status_req_pending(&self) -> bool {
        get_status_req_pending() != 0
    }

    #[inline]
    pub fn get_status_rsp_seen(&self) -> bool {
        get_status_rsp_seen() != 0
    }

    #[inline]
    pub fn get_status_stale_fault(&self) -> bool {
        get_status_stale_fault() != 0
    }

    #[inline]
    pub fn get_status_timeout_fault(&self) -> bool {
        get_status_timeout_fault() != 0
    }

    #[inline]
    pub fn get_status_range_fault(&self) -> bool {
        get_status_range_fault() != 0
    }

    #[inline]
    pub fn get_status_fallback_active(&self) -> bool {
        get_status_fallback_active() != 0
    }

    #[inline]
    pub fn get_status_last_good_valid(&self) -> bool {
        get_status_last_good_valid() != 0
    }

    #[inline]
    pub fn get_status_reserved(&self) -> u32 {
        get_status_reserved() as u32
    }

    #[inline]
    pub fn read_timeout_cfg(&self) -> u32 {
        read_timeout_cfg()
    }

    #[inline]
    pub fn write_timeout_cfg(&self, value: u32) {
        write_timeout_cfg(value)
    }

    #[inline]
    pub fn get_timeout_cfg_timeout_cycles(&self) -> u32 {
        get_timeout_cfg_timeout_cycles() as u32
    }

    #[inline]
    pub fn set_timeout_cfg_timeout_cycles(&self, value: u32) {
        set_timeout_cfg_timeout_cycles(value as u32)
    }

    #[inline]
    pub fn read_stale_cfg(&self) -> u32 {
        read_stale_cfg()
    }

    #[inline]
    pub fn write_stale_cfg(&self, value: u32) {
        write_stale_cfg(value)
    }

    #[inline]
    pub fn get_stale_cfg_stale_cycles(&self) -> u32 {
        get_stale_cfg_stale_cycles() as u32
    }

    #[inline]
    pub fn set_stale_cfg_stale_cycles(&self, value: u32) {
        set_stale_cfg_stale_cycles(value as u32)
    }

    #[inline]
    pub fn read_cmd_min(&self) -> u32 {
        read_cmd_min()
    }

    #[inline]
    pub fn write_cmd_min(&self, value: u32) {
        write_cmd_min(value)
    }

    #[inline]
    pub fn get_cmd_min_cmd_min(&self) -> u16 {
        get_cmd_min_cmd_min() as u16
    }

    #[inline]
    pub fn set_cmd_min_cmd_min(&self, value: u16) {
        set_cmd_min_cmd_min(value as u32)
    }

    #[inline]
    pub fn get_cmd_min_reserved(&self) -> u16 {
        get_cmd_min_reserved() as u16
    }

    #[inline]
    pub fn read_cmd_max(&self) -> u32 {
        read_cmd_max()
    }

    #[inline]
    pub fn write_cmd_max(&self, value: u32) {
        write_cmd_max(value)
    }

    #[inline]
    pub fn get_cmd_max_cmd_max(&self) -> u16 {
        get_cmd_max_cmd_max() as u16
    }

    #[inline]
    pub fn set_cmd_max_cmd_max(&self, value: u16) {
        set_cmd_max_cmd_max(value as u32)
    }

    #[inline]
    pub fn get_cmd_max_reserved(&self) -> u16 {
        get_cmd_max_reserved() as u16
    }

    #[inline]
    pub fn read_cmd_safe(&self) -> u32 {
        read_cmd_safe()
    }

    #[inline]
    pub fn write_cmd_safe(&self, value: u32) {
        write_cmd_safe(value)
    }

    #[inline]
    pub fn get_cmd_safe_cmd_safe(&self) -> u16 {
        get_cmd_safe_cmd_safe() as u16
    }

    #[inline]
    pub fn set_cmd_safe_cmd_safe(&self, value: u16) {
        set_cmd_safe_cmd_safe(value as u32)
    }

    #[inline]
    pub fn get_cmd_safe_reserved(&self) -> u16 {
        get_cmd_safe_reserved() as u16
    }

    #[inline]
    pub fn read_seq_tx(&self) -> u32 {
        read_seq_tx()
    }

    #[inline]
    pub fn write_seq_tx(&self, value: u32) {
        write_seq_tx(value)
    }

    #[inline]
    pub fn get_seq_tx_seq_tx(&self) -> u16 {
        get_seq_tx_seq_tx() as u16
    }

    #[inline]
    pub fn set_seq_tx_seq_tx(&self, value: u16) {
        set_seq_tx_seq_tx(value as u32)
    }

    #[inline]
    pub fn get_seq_tx_reserved(&self) -> u16 {
        get_seq_tx_reserved() as u16
    }

    #[inline]
    pub fn read_seq_rx(&self) -> u32 {
        read_seq_rx()
    }

    #[inline]
    pub fn get_seq_rx_seq_rx(&self) -> u16 {
        get_seq_rx_seq_rx() as u16
    }

    #[inline]
    pub fn get_seq_rx_reserved(&self) -> u16 {
        get_seq_rx_reserved() as u16
    }

    #[inline]
    pub fn read_meta(&self) -> u32 {
        read_meta()
    }

    #[inline]
    pub fn write_meta(&self, value: u32) {
        write_meta(value)
    }

    #[inline]
    pub fn get_meta_velocity_bucket(&self) -> u8 {
        get_meta_velocity_bucket() as u8
    }

    #[inline]
    pub fn set_meta_velocity_bucket(&self, value: u8) {
        set_meta_velocity_bucket(value as u32)
    }

    #[inline]
    pub fn get_meta_mode(&self) -> u8 {
        get_meta_mode() as u8
    }

    #[inline]
    pub fn set_meta_mode(&self, value: u8) {
        set_meta_mode(value as u32)
    }

    #[inline]
    pub fn get_meta_env_flags(&self) -> u8 {
        get_meta_env_flags() as u8
    }

    #[inline]
    pub fn set_meta_env_flags(&self, value: u8) {
        set_meta_env_flags(value as u32)
    }

    #[inline]
    pub fn get_meta_session_id(&self) -> u16 {
        get_meta_session_id() as u16
    }

    #[inline]
    pub fn set_meta_session_id(&self, value: u16) {
        set_meta_session_id(value as u32)
    }

}
