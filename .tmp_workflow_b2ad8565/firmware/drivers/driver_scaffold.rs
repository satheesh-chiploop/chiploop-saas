use crate::hal::registers::*;

pub struct DigitalSubsystemDriver;

impl DigitalSubsystemDriver {
    #[inline]
    pub const fn new() -> Self {
        Self
    }

    #[inline]
    pub fn read_revision_id(&self) -> u32 {
        read_revision_id()
    }

    #[inline]
    pub fn get_revision_id_revision_id(&self) -> u16 {
        get_revision_id_revision_id() as u16
    }

    #[inline]
    pub fn get_revision_id_reserved(&self) -> u32 {
        get_revision_id_reserved() as u32
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
    pub fn get_ctrl_mode(&self) -> u8 {
        get_ctrl_mode() as u8
    }

    #[inline]
    pub fn set_ctrl_mode(&self, value: u8) {
        set_ctrl_mode(value as u32)
    }

    #[inline]
    pub fn get_ctrl_slew_enable(&self) -> bool {
        get_ctrl_slew_enable() != 0
    }

    #[inline]
    pub fn set_ctrl_slew_enable(&self, value: bool) {
        set_ctrl_slew_enable(if value { 1 } else { 0 })
    }

    #[inline]
    pub fn get_ctrl_safe_selector(&self) -> u8 {
        get_ctrl_safe_selector() as u8
    }

    #[inline]
    pub fn set_ctrl_safe_selector(&self, value: u8) {
        set_ctrl_safe_selector(value as u32)
    }

    #[inline]
    pub fn get_ctrl_reserved0(&self) -> u8 {
        get_ctrl_reserved0() as u8
    }

    #[inline]
    pub fn get_ctrl_request_seq_seed(&self) -> u16 {
        get_ctrl_request_seq_seed() as u16
    }

    #[inline]
    pub fn set_ctrl_request_seq_seed(&self, value: u16) {
        set_ctrl_request_seq_seed(value as u32)
    }

    #[inline]
    pub fn get_ctrl_response_age_limit(&self) -> u16 {
        get_ctrl_response_age_limit() as u16
    }

    #[inline]
    pub fn set_ctrl_response_age_limit(&self, value: u16) {
        set_ctrl_response_age_limit(value as u32)
    }

    #[inline]
    pub fn get_ctrl_timeout_threshold(&self) -> u16 {
        get_ctrl_timeout_threshold() as u16
    }

    #[inline]
    pub fn set_ctrl_timeout_threshold(&self, value: u16) {
        set_ctrl_timeout_threshold(value as u32)
    }

    #[inline]
    pub fn read_limits_min(&self) -> u32 {
        read_limits_min()
    }

    #[inline]
    pub fn write_limits_min(&self, value: u32) {
        write_limits_min(value)
    }

    #[inline]
    pub fn get_limits_min_actuator_min(&self) -> u32 {
        get_limits_min_actuator_min() as u32
    }

    #[inline]
    pub fn set_limits_min_actuator_min(&self, value: u32) {
        set_limits_min_actuator_min(value as u32)
    }

    #[inline]
    pub fn get_limits_min_reserved(&self) -> u32 {
        get_limits_min_reserved() as u32
    }

    #[inline]
    pub fn read_limits_max(&self) -> u32 {
        read_limits_max()
    }

    #[inline]
    pub fn write_limits_max(&self, value: u32) {
        write_limits_max(value)
    }

    #[inline]
    pub fn get_limits_max_actuator_max(&self) -> u32 {
        get_limits_max_actuator_max() as u32
    }

    #[inline]
    pub fn set_limits_max_actuator_max(&self, value: u32) {
        set_limits_max_actuator_max(value as u32)
    }

    #[inline]
    pub fn get_limits_max_reserved(&self) -> u32 {
        get_limits_max_reserved() as u32
    }

    #[inline]
    pub fn read_fault_status(&self) -> u32 {
        read_fault_status()
    }

    #[inline]
    pub fn write_fault_status(&self, value: u32) {
        write_fault_status(value)
    }

    #[inline]
    pub fn get_fault_status_fault_status(&self) -> bool {
        get_fault_status_fault_status() != 0
    }

    #[inline]
    pub fn get_fault_status_reserved0(&self) -> u8 {
        get_fault_status_reserved0() as u8
    }

    #[inline]
    pub fn get_fault_status_fault_cause(&self) -> u8 {
        get_fault_status_fault_cause() as u8
    }

    #[inline]
    pub fn get_fault_status_reserved1(&self) -> u32 {
        get_fault_status_reserved1() as u32
    }

    #[inline]
    pub fn read_watchdog_snapshot(&self) -> u32 {
        read_watchdog_snapshot()
    }

    #[inline]
    pub fn get_watchdog_snapshot_timeout_counter_snapshot(&self) -> u16 {
        get_watchdog_snapshot_timeout_counter_snapshot() as u16
    }

    #[inline]
    pub fn get_watchdog_snapshot_request_id_snapshot(&self) -> u16 {
        get_watchdog_snapshot_request_id_snapshot() as u16
    }

    #[inline]
    pub fn get_watchdog_snapshot_last_good_cmd(&self) -> u32 {
        get_watchdog_snapshot_last_good_cmd() as u32
    }

    #[inline]
    pub fn read_status(&self) -> u32 {
        read_status()
    }

    #[inline]
    pub fn get_status_safe_fallback(&self) -> bool {
        get_status_safe_fallback() != 0
    }

    #[inline]
    pub fn get_status_fault_irq(&self) -> bool {
        get_status_fault_irq() != 0
    }

    #[inline]
    pub fn get_status_request_busy(&self) -> bool {
        get_status_request_busy() != 0
    }

    #[inline]
    pub fn get_status_validated_response_valid(&self) -> bool {
        get_status_validated_response_valid() != 0
    }

    #[inline]
    pub fn get_status_actuator_cmd_valid(&self) -> bool {
        get_status_actuator_cmd_valid() != 0
    }

    #[inline]
    pub fn get_status_status_snapshot_valid(&self) -> bool {
        get_status_status_snapshot_valid() != 0
    }

    #[inline]
    pub fn get_status_reserved(&self) -> u32 {
        get_status_reserved() as u32
    }

    #[inline]
    pub fn read_reserved_1(&self) -> u32 {
        read_reserved_1()
    }

    #[inline]
    pub fn get_reserved_1_reserved(&self) -> u32 {
        get_reserved_1_reserved() as u32
    }

}
