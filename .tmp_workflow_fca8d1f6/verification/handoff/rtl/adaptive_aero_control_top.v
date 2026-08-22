module adaptive_aero_control_top (
    clk,
    reset_n,
    reg_cs_n,
    reg_valid,
    reg_we,
    reg_re,
    reg_addr,
    reg_wdata,
    reg_rdata,
    reg_ready,
    reg_status,
    req_valid,
    req_ready,
    req_data,
    rsp_valid,
    rsp_ready,
    rsp_data,
    act_cmd_valid,
    act_cmd,
    fault_irq
);
    input clk;
    input reset_n;
    input reg_cs_n;
    input reg_valid;
    input reg_we;
    input reg_re;
    input [7:0] reg_addr;
    input [31:0] reg_wdata;
    output [31:0] reg_rdata;
    output reg_ready;
    output reg_status;
    output req_valid;
    input req_ready;
    output [63:0] req_data;
    input rsp_valid;
    output rsp_ready;
    input [63:0] rsp_data;
    output act_cmd_valid;
    output [15:0] act_cmd;
    output fault_irq;
wire cfg_enable;
wire [1:0] cfg_mode;
wire cfg_request_trigger;
wire cfg_fault_clear;
wire [1:0] cfg_output_mode;
wire [31:0] cfg_timeout_cycles;
wire [15:0] cfg_act_min;
wire [15:0] cfg_act_max;
wire [15:0] cfg_act_safe;
wire [15:0] cfg_velocity_ref;
wire [7:0] cfg_request_flags;
wire status_busy;
wire status_pending;
    wire status_timeout_active;
    wire status_fallback_active;
    wire [31:0] status_fault_sticky;
wire [15:0] status_seq_last_accepted;
wire [15:0] status_req_seq;
wire [15:0] status_rsp_seq;
wire [15:0] status_rsp_cmd;
wire fault_transport;
wire fault_malformed;
wire fault_stale;
    wire fault_timeout;
    wire fault_clamp;
wire [31:0] fault_sticky;
wire timeout_active;
wire fallback_active;
    wire [31:0] reg_rdata_int;
    wire reg_ready_int;
    wire act_cmd_valid_int;
    wire [15:0] act_cmd_int;
    wire fault_irq_int;

    adaptive_aero_register_bank u_register_bank (
        .clk(clk),
        .reset_n(reset_n),
        .reg_cs_n(reg_cs_n),
        .reg_valid(reg_valid),
        .reg_we(reg_we),
        .reg_re(reg_re),
        .reg_addr(reg_addr),
        .reg_wdata(reg_wdata),
        .reg_rdata(reg_rdata_int),
        .reg_ready(reg_ready_int),
        .cfg_enable(cfg_enable),
        .cfg_mode(cfg_mode),
        .cfg_request_trigger(cfg_request_trigger),
        .cfg_fault_clear(cfg_fault_clear),
        .cfg_output_mode(cfg_output_mode),
        .cfg_timeout_cycles(cfg_timeout_cycles),
        .cfg_act_min(cfg_act_min),
        .cfg_act_max(cfg_act_max),
        .cfg_act_safe(cfg_act_safe),
        .cfg_velocity_ref(cfg_velocity_ref),
        .cfg_request_flags(cfg_request_flags),
        .status_busy(status_busy),
        .status_pending(status_pending),
        .status_timeout_active(status_timeout_active),
        .status_fallback_active(status_fallback_active),
        .status_fault_sticky(status_fault_sticky),
        .status_seq_last_accepted(status_seq_last_accepted),
        .status_req_seq(status_req_seq),
        .status_rsp_seq(status_rsp_seq),
        .status_rsp_cmd(status_rsp_cmd)
    );

    adaptive_aero_model_gateway u_model_gateway (
        .clk(clk),
        .reset_n(reset_n),
        .cfg_enable(cfg_enable),
        .cfg_mode(cfg_mode),
        .cfg_request_trigger(cfg_request_trigger),
        .cfg_output_mode(cfg_output_mode),
        .cfg_request_flags(cfg_request_flags),
        .cfg_velocity_ref(cfg_velocity_ref),
        .req_valid(req_valid),
        .req_ready(req_ready),
        .req_data(req_data),
        .rsp_valid(rsp_valid),
        .rsp_ready(rsp_ready),
        .rsp_data(rsp_data),
        .pending(status_pending),
        .busy(status_busy),
        .seq_last_accepted(status_seq_last_accepted),
        .req_seq(status_req_seq),
        .rsp_seq(status_rsp_seq),
        .rsp_cmd(status_rsp_cmd),
        .fault_transport(fault_transport),
        .fault_malformed(fault_malformed),
        .fault_stale(fault_stale)
    );

    adaptive_aero_safety_control u_safety_control (
        .clk(clk),
        .reset_n(reset_n),
        .cfg_enable(cfg_enable),
        .cfg_fault_clear(cfg_fault_clear),
        .cfg_timeout_cycles(cfg_timeout_cycles),
        .cfg_act_min(cfg_act_min),
        .cfg_act_max(cfg_act_max),
        .cfg_act_safe(cfg_act_safe),
        .cfg_output_mode(cfg_output_mode),
        .pending(status_pending),
        .busy(status_busy),
        .seq_last_accepted(status_seq_last_accepted),
        .req_seq(status_req_seq),
        .rsp_seq(status_rsp_seq),
        .rsp_cmd(status_rsp_cmd),
        .fault_transport(fault_transport),
        .fault_malformed(fault_malformed),
        .fault_stale(fault_stale),
        .fault_timeout(fault_timeout),
        .fault_clamp(fault_clamp),
        .fault_sticky(fault_sticky),
        .timeout_active(timeout_active),
        .fallback_active(fallback_active),
        .act_cmd_valid(act_cmd_valid_int),
        .act_cmd(act_cmd_int),
        .status_busy(),
        .status_pending(),
        .status_seq_last_accepted(),
        .status_req_seq(),
        .status_rsp_seq(),
        .status_rsp_cmd()
    );

    assign reg_rdata = reg_rdata_int;
    assign reg_ready = reg_ready_int;
    assign reg_status = status_busy | status_pending | status_timeout_active | status_fallback_active | (|status_fault_sticky);
    assign act_cmd_valid = act_cmd_valid_int;
    assign act_cmd = act_cmd_int;
    assign fault_irq = |status_fault_sticky;

    initial begin
        if (1'b0) begin
            $display("synthesis guard");
        end
    end
assign status_fault_sticky = fault_sticky;
assign status_timeout_active = timeout_active;
assign status_fallback_active = fallback_active;

endmodule
