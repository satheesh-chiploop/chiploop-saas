use core::ptr::{read_volatile, write_volatile};

pub const BASE_ADDRESS: usize = 0x00000000;

pub const CTRL_OFFSET: usize = 0x00000000;
pub const CTRL_ENABLE_SHIFT: u32 = 0;
pub const CTRL_ENABLE_WIDTH: u32 = 1;
pub const CTRL_ENABLE_MASK: u32 = 0x00000001;
pub const CTRL_CLEAR_FAULT_SHIFT: u32 = 1;
pub const CTRL_CLEAR_FAULT_WIDTH: u32 = 1;
pub const CTRL_CLEAR_FAULT_MASK: u32 = 0x00000002;
pub const CTRL_ARM_OUTPUT_SHIFT: u32 = 2;
pub const CTRL_ARM_OUTPUT_WIDTH: u32 = 1;
pub const CTRL_ARM_OUTPUT_MASK: u32 = 0x00000004;
pub const CTRL_REQUEST_START_SHIFT: u32 = 3;
pub const CTRL_REQUEST_START_WIDTH: u32 = 1;
pub const CTRL_REQUEST_START_MASK: u32 = 0x00000008;
pub const CTRL_BYPASS_MODEL_SHIFT: u32 = 4;
pub const CTRL_BYPASS_MODEL_WIDTH: u32 = 1;
pub const CTRL_BYPASS_MODEL_MASK: u32 = 0x00000010;
pub const CTRL_RESERVED_SHIFT: u32 = 5;
pub const CTRL_RESERVED_WIDTH: u32 = 27;
pub const CTRL_RESERVED_MASK: u32 = 0xFFFFFFE0;
pub const STATUS_OFFSET: usize = 0x00000004;
pub const STATUS_BUSY_SHIFT: u32 = 0;
pub const STATUS_BUSY_WIDTH: u32 = 1;
pub const STATUS_BUSY_MASK: u32 = 0x00000001;
pub const STATUS_REQ_PENDING_SHIFT: u32 = 1;
pub const STATUS_REQ_PENDING_WIDTH: u32 = 1;
pub const STATUS_REQ_PENDING_MASK: u32 = 0x00000002;
pub const STATUS_RSP_SEEN_SHIFT: u32 = 2;
pub const STATUS_RSP_SEEN_WIDTH: u32 = 1;
pub const STATUS_RSP_SEEN_MASK: u32 = 0x00000004;
pub const STATUS_STALE_FAULT_SHIFT: u32 = 3;
pub const STATUS_STALE_FAULT_WIDTH: u32 = 1;
pub const STATUS_STALE_FAULT_MASK: u32 = 0x00000008;
pub const STATUS_TIMEOUT_FAULT_SHIFT: u32 = 4;
pub const STATUS_TIMEOUT_FAULT_WIDTH: u32 = 1;
pub const STATUS_TIMEOUT_FAULT_MASK: u32 = 0x00000010;
pub const STATUS_RANGE_FAULT_SHIFT: u32 = 5;
pub const STATUS_RANGE_FAULT_WIDTH: u32 = 1;
pub const STATUS_RANGE_FAULT_MASK: u32 = 0x00000020;
pub const STATUS_FALLBACK_ACTIVE_SHIFT: u32 = 6;
pub const STATUS_FALLBACK_ACTIVE_WIDTH: u32 = 1;
pub const STATUS_FALLBACK_ACTIVE_MASK: u32 = 0x00000040;
pub const STATUS_LAST_GOOD_VALID_SHIFT: u32 = 7;
pub const STATUS_LAST_GOOD_VALID_WIDTH: u32 = 1;
pub const STATUS_LAST_GOOD_VALID_MASK: u32 = 0x00000080;
pub const STATUS_RESERVED_SHIFT: u32 = 8;
pub const STATUS_RESERVED_WIDTH: u32 = 24;
pub const STATUS_RESERVED_MASK: u32 = 0xFFFFFF00;
pub const TIMEOUT_CFG_OFFSET: usize = 0x00000008;
pub const TIMEOUT_CFG_TIMEOUT_CYCLES_SHIFT: u32 = 0;
pub const TIMEOUT_CFG_TIMEOUT_CYCLES_WIDTH: u32 = 32;
pub const TIMEOUT_CFG_TIMEOUT_CYCLES_MASK: u32 = 0xFFFFFFFF;
pub const STALE_CFG_OFFSET: usize = 0x0000000C;
pub const STALE_CFG_STALE_CYCLES_SHIFT: u32 = 0;
pub const STALE_CFG_STALE_CYCLES_WIDTH: u32 = 32;
pub const STALE_CFG_STALE_CYCLES_MASK: u32 = 0xFFFFFFFF;
pub const CMD_MIN_OFFSET: usize = 0x00000010;
pub const CMD_MIN_CMD_MIN_SHIFT: u32 = 0;
pub const CMD_MIN_CMD_MIN_WIDTH: u32 = 16;
pub const CMD_MIN_CMD_MIN_MASK: u32 = 0x0000FFFF;
pub const CMD_MIN_RESERVED_SHIFT: u32 = 16;
pub const CMD_MIN_RESERVED_WIDTH: u32 = 16;
pub const CMD_MIN_RESERVED_MASK: u32 = 0xFFFF0000;
pub const CMD_MAX_OFFSET: usize = 0x00000014;
pub const CMD_MAX_CMD_MAX_SHIFT: u32 = 0;
pub const CMD_MAX_CMD_MAX_WIDTH: u32 = 16;
pub const CMD_MAX_CMD_MAX_MASK: u32 = 0x0000FFFF;
pub const CMD_MAX_RESERVED_SHIFT: u32 = 16;
pub const CMD_MAX_RESERVED_WIDTH: u32 = 16;
pub const CMD_MAX_RESERVED_MASK: u32 = 0xFFFF0000;
pub const CMD_SAFE_OFFSET: usize = 0x00000018;
pub const CMD_SAFE_CMD_SAFE_SHIFT: u32 = 0;
pub const CMD_SAFE_CMD_SAFE_WIDTH: u32 = 16;
pub const CMD_SAFE_CMD_SAFE_MASK: u32 = 0x0000FFFF;
pub const CMD_SAFE_RESERVED_SHIFT: u32 = 16;
pub const CMD_SAFE_RESERVED_WIDTH: u32 = 16;
pub const CMD_SAFE_RESERVED_MASK: u32 = 0xFFFF0000;
pub const SEQ_TX_OFFSET: usize = 0x0000001C;
pub const SEQ_TX_SEQ_TX_SHIFT: u32 = 0;
pub const SEQ_TX_SEQ_TX_WIDTH: u32 = 16;
pub const SEQ_TX_SEQ_TX_MASK: u32 = 0x0000FFFF;
pub const SEQ_TX_RESERVED_SHIFT: u32 = 16;
pub const SEQ_TX_RESERVED_WIDTH: u32 = 16;
pub const SEQ_TX_RESERVED_MASK: u32 = 0xFFFF0000;
pub const SEQ_RX_OFFSET: usize = 0x00000020;
pub const SEQ_RX_SEQ_RX_SHIFT: u32 = 0;
pub const SEQ_RX_SEQ_RX_WIDTH: u32 = 16;
pub const SEQ_RX_SEQ_RX_MASK: u32 = 0x0000FFFF;
pub const SEQ_RX_RESERVED_SHIFT: u32 = 16;
pub const SEQ_RX_RESERVED_WIDTH: u32 = 16;
pub const SEQ_RX_RESERVED_MASK: u32 = 0xFFFF0000;
pub const META_OFFSET: usize = 0x00000024;
pub const META_VELOCITY_BUCKET_SHIFT: u32 = 0;
pub const META_VELOCITY_BUCKET_WIDTH: u32 = 8;
pub const META_VELOCITY_BUCKET_MASK: u32 = 0x000000FF;
pub const META_MODE_SHIFT: u32 = 8;
pub const META_MODE_WIDTH: u32 = 4;
pub const META_MODE_MASK: u32 = 0x00000F00;
pub const META_ENV_FLAGS_SHIFT: u32 = 12;
pub const META_ENV_FLAGS_WIDTH: u32 = 4;
pub const META_ENV_FLAGS_MASK: u32 = 0x0000F000;
pub const META_SESSION_ID_SHIFT: u32 = 16;
pub const META_SESSION_ID_WIDTH: u32 = 16;
pub const META_SESSION_ID_MASK: u32 = 0xFFFF0000;

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
pub fn read_ctrl() -> u32 {
    read_reg(CTRL_OFFSET)
}

#[inline]
pub fn write_ctrl(value: u32) {
    write_reg(CTRL_OFFSET, value)
}

#[inline]
pub fn get_ctrl_enable() -> u32 {
    (read_ctrl() & CTRL_ENABLE_MASK) >> CTRL_ENABLE_SHIFT
}

#[inline]
pub fn set_ctrl_enable(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_ENABLE_MASK) | ((value << CTRL_ENABLE_SHIFT) & CTRL_ENABLE_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_clear_fault() -> u32 {
    (read_ctrl() & CTRL_CLEAR_FAULT_MASK) >> CTRL_CLEAR_FAULT_SHIFT
}

#[inline]
pub fn set_ctrl_clear_fault(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_CLEAR_FAULT_MASK) | ((value << CTRL_CLEAR_FAULT_SHIFT) & CTRL_CLEAR_FAULT_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_arm_output() -> u32 {
    (read_ctrl() & CTRL_ARM_OUTPUT_MASK) >> CTRL_ARM_OUTPUT_SHIFT
}

#[inline]
pub fn set_ctrl_arm_output(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_ARM_OUTPUT_MASK) | ((value << CTRL_ARM_OUTPUT_SHIFT) & CTRL_ARM_OUTPUT_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_request_start() -> u32 {
    (read_ctrl() & CTRL_REQUEST_START_MASK) >> CTRL_REQUEST_START_SHIFT
}

#[inline]
pub fn set_ctrl_request_start(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_REQUEST_START_MASK) | ((value << CTRL_REQUEST_START_SHIFT) & CTRL_REQUEST_START_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_bypass_model() -> u32 {
    (read_ctrl() & CTRL_BYPASS_MODEL_MASK) >> CTRL_BYPASS_MODEL_SHIFT
}

#[inline]
pub fn set_ctrl_bypass_model(value: u32) {
    let current = read_ctrl();
    let next = (current & !CTRL_BYPASS_MODEL_MASK) | ((value << CTRL_BYPASS_MODEL_SHIFT) & CTRL_BYPASS_MODEL_MASK);
    write_ctrl(next);
}

#[inline]
pub fn get_ctrl_reserved() -> u32 {
    (read_ctrl() & CTRL_RESERVED_MASK) >> CTRL_RESERVED_SHIFT
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
pub fn get_status_req_pending() -> u32 {
    (read_status() & STATUS_REQ_PENDING_MASK) >> STATUS_REQ_PENDING_SHIFT
}

#[inline]
pub fn get_status_rsp_seen() -> u32 {
    (read_status() & STATUS_RSP_SEEN_MASK) >> STATUS_RSP_SEEN_SHIFT
}

#[inline]
pub fn get_status_stale_fault() -> u32 {
    (read_status() & STATUS_STALE_FAULT_MASK) >> STATUS_STALE_FAULT_SHIFT
}

#[inline]
pub fn get_status_timeout_fault() -> u32 {
    (read_status() & STATUS_TIMEOUT_FAULT_MASK) >> STATUS_TIMEOUT_FAULT_SHIFT
}

#[inline]
pub fn get_status_range_fault() -> u32 {
    (read_status() & STATUS_RANGE_FAULT_MASK) >> STATUS_RANGE_FAULT_SHIFT
}

#[inline]
pub fn get_status_fallback_active() -> u32 {
    (read_status() & STATUS_FALLBACK_ACTIVE_MASK) >> STATUS_FALLBACK_ACTIVE_SHIFT
}

#[inline]
pub fn get_status_last_good_valid() -> u32 {
    (read_status() & STATUS_LAST_GOOD_VALID_MASK) >> STATUS_LAST_GOOD_VALID_SHIFT
}

#[inline]
pub fn get_status_reserved() -> u32 {
    (read_status() & STATUS_RESERVED_MASK) >> STATUS_RESERVED_SHIFT
}

#[inline]
pub fn read_timeout_cfg() -> u32 {
    read_reg(TIMEOUT_CFG_OFFSET)
}

#[inline]
pub fn write_timeout_cfg(value: u32) {
    write_reg(TIMEOUT_CFG_OFFSET, value)
}

#[inline]
pub fn get_timeout_cfg_timeout_cycles() -> u32 {
    (read_timeout_cfg() & TIMEOUT_CFG_TIMEOUT_CYCLES_MASK) >> TIMEOUT_CFG_TIMEOUT_CYCLES_SHIFT
}

#[inline]
pub fn set_timeout_cfg_timeout_cycles(value: u32) {
    let current = read_timeout_cfg();
    let next = (current & !TIMEOUT_CFG_TIMEOUT_CYCLES_MASK) | ((value << TIMEOUT_CFG_TIMEOUT_CYCLES_SHIFT) & TIMEOUT_CFG_TIMEOUT_CYCLES_MASK);
    write_timeout_cfg(next);
}

#[inline]
pub fn read_stale_cfg() -> u32 {
    read_reg(STALE_CFG_OFFSET)
}

#[inline]
pub fn write_stale_cfg(value: u32) {
    write_reg(STALE_CFG_OFFSET, value)
}

#[inline]
pub fn get_stale_cfg_stale_cycles() -> u32 {
    (read_stale_cfg() & STALE_CFG_STALE_CYCLES_MASK) >> STALE_CFG_STALE_CYCLES_SHIFT
}

#[inline]
pub fn set_stale_cfg_stale_cycles(value: u32) {
    let current = read_stale_cfg();
    let next = (current & !STALE_CFG_STALE_CYCLES_MASK) | ((value << STALE_CFG_STALE_CYCLES_SHIFT) & STALE_CFG_STALE_CYCLES_MASK);
    write_stale_cfg(next);
}

#[inline]
pub fn read_cmd_min() -> u32 {
    read_reg(CMD_MIN_OFFSET)
}

#[inline]
pub fn write_cmd_min(value: u32) {
    write_reg(CMD_MIN_OFFSET, value)
}

#[inline]
pub fn get_cmd_min_cmd_min() -> u32 {
    (read_cmd_min() & CMD_MIN_CMD_MIN_MASK) >> CMD_MIN_CMD_MIN_SHIFT
}

#[inline]
pub fn set_cmd_min_cmd_min(value: u32) {
    let current = read_cmd_min();
    let next = (current & !CMD_MIN_CMD_MIN_MASK) | ((value << CMD_MIN_CMD_MIN_SHIFT) & CMD_MIN_CMD_MIN_MASK);
    write_cmd_min(next);
}

#[inline]
pub fn get_cmd_min_reserved() -> u32 {
    (read_cmd_min() & CMD_MIN_RESERVED_MASK) >> CMD_MIN_RESERVED_SHIFT
}

#[inline]
pub fn read_cmd_max() -> u32 {
    read_reg(CMD_MAX_OFFSET)
}

#[inline]
pub fn write_cmd_max(value: u32) {
    write_reg(CMD_MAX_OFFSET, value)
}

#[inline]
pub fn get_cmd_max_cmd_max() -> u32 {
    (read_cmd_max() & CMD_MAX_CMD_MAX_MASK) >> CMD_MAX_CMD_MAX_SHIFT
}

#[inline]
pub fn set_cmd_max_cmd_max(value: u32) {
    let current = read_cmd_max();
    let next = (current & !CMD_MAX_CMD_MAX_MASK) | ((value << CMD_MAX_CMD_MAX_SHIFT) & CMD_MAX_CMD_MAX_MASK);
    write_cmd_max(next);
}

#[inline]
pub fn get_cmd_max_reserved() -> u32 {
    (read_cmd_max() & CMD_MAX_RESERVED_MASK) >> CMD_MAX_RESERVED_SHIFT
}

#[inline]
pub fn read_cmd_safe() -> u32 {
    read_reg(CMD_SAFE_OFFSET)
}

#[inline]
pub fn write_cmd_safe(value: u32) {
    write_reg(CMD_SAFE_OFFSET, value)
}

#[inline]
pub fn get_cmd_safe_cmd_safe() -> u32 {
    (read_cmd_safe() & CMD_SAFE_CMD_SAFE_MASK) >> CMD_SAFE_CMD_SAFE_SHIFT
}

#[inline]
pub fn set_cmd_safe_cmd_safe(value: u32) {
    let current = read_cmd_safe();
    let next = (current & !CMD_SAFE_CMD_SAFE_MASK) | ((value << CMD_SAFE_CMD_SAFE_SHIFT) & CMD_SAFE_CMD_SAFE_MASK);
    write_cmd_safe(next);
}

#[inline]
pub fn get_cmd_safe_reserved() -> u32 {
    (read_cmd_safe() & CMD_SAFE_RESERVED_MASK) >> CMD_SAFE_RESERVED_SHIFT
}

#[inline]
pub fn read_seq_tx() -> u32 {
    read_reg(SEQ_TX_OFFSET)
}

#[inline]
pub fn write_seq_tx(value: u32) {
    write_reg(SEQ_TX_OFFSET, value)
}

#[inline]
pub fn get_seq_tx_seq_tx() -> u32 {
    (read_seq_tx() & SEQ_TX_SEQ_TX_MASK) >> SEQ_TX_SEQ_TX_SHIFT
}

#[inline]
pub fn set_seq_tx_seq_tx(value: u32) {
    let current = read_seq_tx();
    let next = (current & !SEQ_TX_SEQ_TX_MASK) | ((value << SEQ_TX_SEQ_TX_SHIFT) & SEQ_TX_SEQ_TX_MASK);
    write_seq_tx(next);
}

#[inline]
pub fn get_seq_tx_reserved() -> u32 {
    (read_seq_tx() & SEQ_TX_RESERVED_MASK) >> SEQ_TX_RESERVED_SHIFT
}

#[inline]
pub fn read_seq_rx() -> u32 {
    read_reg(SEQ_RX_OFFSET)
}

#[inline]
pub fn get_seq_rx_seq_rx() -> u32 {
    (read_seq_rx() & SEQ_RX_SEQ_RX_MASK) >> SEQ_RX_SEQ_RX_SHIFT
}

#[inline]
pub fn get_seq_rx_reserved() -> u32 {
    (read_seq_rx() & SEQ_RX_RESERVED_MASK) >> SEQ_RX_RESERVED_SHIFT
}

#[inline]
pub fn read_meta() -> u32 {
    read_reg(META_OFFSET)
}

#[inline]
pub fn write_meta(value: u32) {
    write_reg(META_OFFSET, value)
}

#[inline]
pub fn get_meta_velocity_bucket() -> u32 {
    (read_meta() & META_VELOCITY_BUCKET_MASK) >> META_VELOCITY_BUCKET_SHIFT
}

#[inline]
pub fn set_meta_velocity_bucket(value: u32) {
    let current = read_meta();
    let next = (current & !META_VELOCITY_BUCKET_MASK) | ((value << META_VELOCITY_BUCKET_SHIFT) & META_VELOCITY_BUCKET_MASK);
    write_meta(next);
}

#[inline]
pub fn get_meta_mode() -> u32 {
    (read_meta() & META_MODE_MASK) >> META_MODE_SHIFT
}

#[inline]
pub fn set_meta_mode(value: u32) {
    let current = read_meta();
    let next = (current & !META_MODE_MASK) | ((value << META_MODE_SHIFT) & META_MODE_MASK);
    write_meta(next);
}

#[inline]
pub fn get_meta_env_flags() -> u32 {
    (read_meta() & META_ENV_FLAGS_MASK) >> META_ENV_FLAGS_SHIFT
}

#[inline]
pub fn set_meta_env_flags(value: u32) {
    let current = read_meta();
    let next = (current & !META_ENV_FLAGS_MASK) | ((value << META_ENV_FLAGS_SHIFT) & META_ENV_FLAGS_MASK);
    write_meta(next);
}

#[inline]
pub fn get_meta_session_id() -> u32 {
    (read_meta() & META_SESSION_ID_MASK) >> META_SESSION_ID_SHIFT
}

#[inline]
pub fn set_meta_session_id(value: u32) {
    let current = read_meta();
    let next = (current & !META_SESSION_ID_MASK) | ((value << META_SESSION_ID_SHIFT) & META_SESSION_ID_MASK);
    write_meta(next);
}

