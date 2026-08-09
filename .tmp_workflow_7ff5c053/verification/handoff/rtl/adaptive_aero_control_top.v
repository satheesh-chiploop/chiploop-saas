module adaptive_aero_control_top (
    clk,
    rst_n,
    cfg_addr,
    cfg_wdata,
    cfg_rdata,
    cfg_we,
    cfg_re,
    cmd_rsp_valid,
    cmd_rsp_ready,
    cmd_rsp_data,
    resp_valid,
    resp_ready,
    resp_data,
    actuator_out,
    status_out
);
    input clk;
    input rst_n;
    input [5:0] cfg_addr;
    input [63:0] cfg_wdata;
    output [63:0] cfg_rdata;
    input cfg_we;
    input cfg_re;
    output cmd_rsp_valid;
    input cmd_rsp_ready;
    output [127:0] cmd_rsp_data;
    input resp_valid;
    output resp_ready;
    input [127:0] resp_data;
    output [15:0] actuator_out;
    output [15:0] status_out;
    wire cfg_enable;
    wire [15:0] operating_velocity_mps;
    wire [15:0] response_timeout_cycles;
    wire [15:0] request_age_limit_cycles;
    wire [15:0] actuator_min_limit;
    wire [15:0] actuator_max_limit;
    wire [15:0] safe_fallback_setpoint;
    wire [3:0] mode_select;
    wire [7:0] geometry_ref_id;
    wire config_error;

wire [15:0] cfg_window_decoder_actuator_max_limit;
wire [15:0] cfg_window_decoder_actuator_min_limit;
wire cfg_window_decoder_cfg_enable;
wire cfg_window_decoder_config_error;
wire [7:0] cfg_window_decoder_geometry_ref_id;
wire [3:0] cfg_window_decoder_mode_select;
wire [15:0] cfg_window_decoder_operating_velocity_mps;
wire [15:0] cfg_window_decoder_request_age_limit_cycles;
wire [15:0] cfg_window_decoder_response_timeout_cycles;
wire [15:0] cfg_window_decoder_safe_fallback_setpoint;
    cfg_window_decoder u_cfg_window_decoder (
        .clk(clk),
        .rst_n(rst_n),
        .cfg_addr(cfg_addr),
        .cfg_wdata(cfg_wdata),
        .cfg_we(cfg_we),
        .cfg_re(cfg_re),
        .cfg_rdata(cfg_rdata),
        .cfg_enable(cfg_enable),
        .operating_velocity_mps(operating_velocity_mps),
        .response_timeout_cycles(response_timeout_cycles),
        .request_age_limit_cycles(request_age_limit_cycles),
        .actuator_min_limit(actuator_min_limit),
        .actuator_max_limit(actuator_max_limit),
        .safe_fallback_setpoint(safe_fallback_setpoint),
        .mode_select(mode_select),
        .geometry_ref_id(geometry_ref_id),
        .config_error(config_error)
    );

    adaptive_request_response_controller u_adaptive_request_response_controller (
        .clk(clk),
        .rst_n(rst_n),
        .cfg_enable(cfg_enable),
        .operating_velocity_mps(operating_velocity_mps),
        .response_timeout_cycles(response_timeout_cycles),
        .request_age_limit_cycles(request_age_limit_cycles),
        .actuator_min_limit(actuator_min_limit),
        .actuator_max_limit(actuator_max_limit),
        .safe_fallback_setpoint(safe_fallback_setpoint),
        .mode_select(mode_select),
        .geometry_ref_id(geometry_ref_id),
        .config_error(config_error),
        .cmd_rsp_ready(cmd_rsp_ready),
        .cmd_rsp_valid(cmd_rsp_valid),
        .cmd_rsp_data(cmd_rsp_data),
        .resp_valid(resp_valid),
        .resp_data(resp_data),
        .resp_ready(resp_ready),
        .actuator_out(actuator_out),
        .status_out(status_out),
        .transaction_id_echo(),
        .busy(),
        .request_pending(),
        .response_valid(),
        .stale_reject(),
        .timeout_fault(),
        .clamp_active(),
        .fallback_active()
    );
endmodule
