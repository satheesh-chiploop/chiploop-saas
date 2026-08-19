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
    pub fn get_ctrl_arm(&self) -> bool {
        get_ctrl_arm() != 0
    }

    #[inline]
    pub fn set_ctrl_arm(&self, value: bool) {
        set_ctrl_arm(if value { 1 } else { 0 })
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
    pub fn get_ctrl_irq_enable(&self) -> u8 {
        get_ctrl_irq_enable() as u8
    }

    #[inline]
    pub fn set_ctrl_irq_enable(&self, value: u8) {
        set_ctrl_irq_enable(value as u32)
    }

    #[inline]
    pub fn read_velocity_setpoint(&self) -> u32 {
        read_velocity_setpoint()
    }

    #[inline]
    pub fn write_velocity_setpoint(&self, value: u32) {
        write_velocity_setpoint(value)
    }

    #[inline]
    pub fn get_velocity_setpoint_velocity_setpoint(&self) -> u32 {
        get_velocity_setpoint_velocity_setpoint() as u32
    }

    #[inline]
    pub fn set_velocity_setpoint_velocity_setpoint(&self, value: u32) {
        set_velocity_setpoint_velocity_setpoint(value as u32)
    }

    #[inline]
    pub fn read_clamp_min(&self) -> u32 {
        read_clamp_min()
    }

    #[inline]
    pub fn write_clamp_min(&self, value: u32) {
        write_clamp_min(value)
    }

    #[inline]
    pub fn get_clamp_min_clamp_min(&self) -> u32 {
        get_clamp_min_clamp_min() as u32
    }

    #[inline]
    pub fn set_clamp_min_clamp_min(&self, value: u32) {
        set_clamp_min_clamp_min(value as u32)
    }

    #[inline]
    pub fn read_clamp_max(&self) -> u32 {
        read_clamp_max()
    }

    #[inline]
    pub fn write_clamp_max(&self, value: u32) {
        write_clamp_max(value)
    }

    #[inline]
    pub fn get_clamp_max_clamp_max(&self) -> u32 {
        get_clamp_max_clamp_max() as u32
    }

    #[inline]
    pub fn set_clamp_max_clamp_max(&self, value: u32) {
        set_clamp_max_clamp_max(value as u32)
    }

    #[inline]
    pub fn read_timeout_threshold(&self) -> u32 {
        read_timeout_threshold()
    }

    #[inline]
    pub fn write_timeout_threshold(&self, value: u32) {
        write_timeout_threshold(value)
    }

    #[inline]
    pub fn get_timeout_threshold_timeout_threshold(&self) -> u16 {
        get_timeout_threshold_timeout_threshold() as u16
    }

    #[inline]
    pub fn set_timeout_threshold_timeout_threshold(&self, value: u16) {
        set_timeout_threshold_timeout_threshold(value as u32)
    }

    #[inline]
    pub fn read_sequence_counter(&self) -> u32 {
        read_sequence_counter()
    }

    #[inline]
    pub fn write_sequence_counter(&self, value: u32) {
        write_sequence_counter(value)
    }

    #[inline]
    pub fn get_sequence_counter_sequence_counter(&self) -> u16 {
        get_sequence_counter_sequence_counter() as u16
    }

    #[inline]
    pub fn set_sequence_counter_sequence_counter(&self, value: u16) {
        set_sequence_counter_sequence_counter(value as u32)
    }

    #[inline]
    pub fn read_fault_clear_w1c(&self) -> u32 {
        read_fault_clear_w1c()
    }

    #[inline]
    pub fn write_fault_clear_w1c(&self, value: u32) {
        write_fault_clear_w1c(value)
    }

    #[inline]
    pub fn get_fault_clear_w1c_fault_clear_w1c(&self) -> u8 {
        get_fault_clear_w1c_fault_clear_w1c() as u8
    }

    #[inline]
    pub fn set_fault_clear_w1c_fault_clear_w1c(&self, value: u8) {
        set_fault_clear_w1c_fault_clear_w1c(value as u32)
    }

    #[inline]
    pub fn read_status(&self) -> u32 {
        read_status()
    }

    #[inline]
    pub fn get_status_fault_sticky(&self) -> u8 {
        get_status_fault_sticky() as u8
    }

    #[inline]
    pub fn get_status_response_ready(&self) -> bool {
        get_status_response_ready() != 0
    }

    #[inline]
    pub fn get_status_fresh(&self) -> bool {
        get_status_fresh() != 0
    }

    #[inline]
    pub fn get_status_stale(&self) -> bool {
        get_status_stale() != 0
    }

    #[inline]
    pub fn get_status_timeout(&self) -> bool {
        get_status_timeout() != 0
    }

    #[inline]
    pub fn get_status_last_seen_sequence(&self) -> u16 {
        get_status_last_seen_sequence() as u16
    }

    #[inline]
    pub fn read_actuator_cmd(&self) -> u32 {
        read_actuator_cmd()
    }

    #[inline]
    pub fn get_actuator_cmd_actuator_cmd(&self) -> u32 {
        get_actuator_cmd_actuator_cmd() as u32
    }

    #[inline]
    pub fn read_irq_status(&self) -> u32 {
        read_irq_status()
    }

    #[inline]
    pub fn get_irq_status_response_ready(&self) -> bool {
        get_irq_status_response_ready() != 0
    }

    #[inline]
    pub fn get_irq_status_stale(&self) -> bool {
        get_irq_status_stale() != 0
    }

    #[inline]
    pub fn get_irq_status_timeout(&self) -> bool {
        get_irq_status_timeout() != 0
    }

    #[inline]
    pub fn get_irq_status_fault(&self) -> bool {
        get_irq_status_fault() != 0
    }

}
