module adaptive_aero_control_top (
    clk,
    reset_n,
    apb_ctrl_addr,
    apb_ctrl_wdata,
    apb_ctrl_valid,
    apb_ctrl_write,
    apb_ctrl_ready,
    apb_ctrl_rdata,
    apb_ctrl_rvalid,
    host_req_stream_valid,
    host_req_stream_data,
    host_req_stream_ready,
    host_resp_stream_valid,
    host_resp_stream_data,
    host_resp_stream_ready,
    actuator_cmd_bus,
    irq,
    reg_fault_sticky,
    req_fifo_pop,
    req_fifo_full,
    req_fifo_empty
);
    input clk;
    input reset_n;
    input [7:0] apb_ctrl_addr;
    input [63:0] apb_ctrl_wdata;
    input apb_ctrl_valid;
    input apb_ctrl_write;
    output apb_ctrl_ready;
    output [63:0] apb_ctrl_rdata;
    output apb_ctrl_rvalid;
    output host_req_stream_valid;
    output [127:0] host_req_stream_data;
    input host_req_stream_ready;
    input host_resp_stream_valid;
    input [127:0] host_resp_stream_data;
    output host_resp_stream_ready;
    output [31:0] actuator_cmd_bus;
    output irq;
    input [15:0] reg_fault_sticky;
    input req_fifo_pop;
    input req_fifo_full;
    input req_fifo_empty;
wire cfg_enable;
wire cfg_soft_reset;
wire cfg_arm_request;
wire cfg_clear_fault;
wire [15:0] cfg_operating_velocity_mps;
wire [23:0] cfg_timeout_cycles;
wire [3:0] cfg_max_outstanding;
wire [15:0] cfg_clamp_min;
wire [15:0] cfg_clamp_max;
wire [15:0] cfg_request_seq;
wire [15:0] cfg_response_seq;
wire [7:0] cfg_fault_status;
wire [7:0] cfg_mode_status;
wire cfg_irq_enable;
wire [63:0] reg_read_data;
wire reg_read_valid;
wire reg_write_accept;
wire reg_request_pending;
wire reg_fallback_active;
wire req_launch_pulse;
    wire [15:0] req_seq_out;
    wire [127:0] req_packet_128;
wire req_fifo_push;
wire [127:0] rsp_packet_128;
wire rsp_accept_pulse;
wire rsp_valid_result;
wire rsp_discard_pulse;
    wire [15:0] rsp_match_seq;
    wire [15:0] last_request_id;
    wire [15:0] last_accepted_response_id;
    wire [15:0] discarded_response_count;
    wire [15:0] timeout_event_count;
    wire [15:0] stale_event_count;
wire fault_timeout_sticky;
wire fault_stale_sticky;
wire fault_invalid_sticky;
wire fault_queue_full_sticky;
wire fault_host_not_ready_sticky;
    wire [7:0] last_fault_code;
    wire act_cmd_enable;
    wire act_cmd_valid;
    wire [15:0] act_cmd_pos;
    wire [11:0] act_cmd_rate;
    wire act_cmd_fault_latched;
    wire fallback_active;

    adaptive_aero_register_map u_regmap (
        .clk(clk),
        .reset_n(reset_n),
        .apb_ctrl_addr(apb_ctrl_addr),
        .apb_ctrl_wdata(apb_ctrl_wdata),
        .apb_ctrl_valid(apb_ctrl_valid),
        .apb_ctrl_write(apb_ctrl_write),
        .apb_ctrl_ready(apb_ctrl_ready),
        .apb_ctrl_rdata(apb_ctrl_rdata),
        .apb_ctrl_rvalid(apb_ctrl_rvalid),
        .cfg_enable(cfg_enable),
        .cfg_soft_reset(cfg_soft_reset),
        .cfg_arm_request(cfg_arm_request),
        .cfg_clear_fault(cfg_clear_fault),
        .cfg_operating_velocity_mps(cfg_operating_velocity_mps),
        .cfg_timeout_cycles(cfg_timeout_cycles),
        .cfg_max_outstanding(cfg_max_outstanding),
        .cfg_clamp_min(cfg_clamp_min),
        .cfg_clamp_max(cfg_clamp_max),
        .cfg_request_seq(cfg_request_seq),
        .cfg_response_seq(cfg_response_seq),
        .cfg_fault_status(cfg_fault_status),
        .cfg_mode_status(cfg_mode_status),
        .cfg_irq_enable(cfg_irq_enable),
        .reg_read_data(reg_read_data),
        .reg_read_valid(reg_read_valid),
        .reg_write_accept(reg_write_accept),
        .reg_fault_sticky(reg_fault_sticky),
        .reg_request_pending(reg_request_pending),
        .reg_fallback_active(reg_fallback_active)
    );

    adaptive_aero_request_engine u_req (
        .clk(clk),
        .reset_n(reset_n),
        .cfg_enable(cfg_enable),
        .cfg_arm_request(cfg_arm_request),
        .cfg_clear_fault(cfg_soft_reset),
        .cfg_operating_velocity_mps(cfg_operating_velocity_mps),
        .cfg_timeout_cycles(cfg_timeout_cycles),
        .cfg_max_outstanding(cfg_max_outstanding),
        .cfg_mode_status(cfg_mode_status),
        .cfg_request_seq(cfg_request_seq),
        .host_req_stream_ready(host_req_stream_ready),
        .req_launch_pulse(req_launch_pulse),
        .req_seq_out(req_seq_out),
        .req_packet_128(req_packet_128),
        .req_fifo_push(req_fifo_push),
        .req_fifo_pop(req_fifo_pop),
        .req_fifo_full(req_fifo_full),
        .req_fifo_empty(req_fifo_empty),
        .reg_request_pending(reg_request_pending),
        .last_request_id(last_request_id),
        .fault_queue_full_sticky(fault_queue_full_sticky),
        .fault_host_not_ready_sticky(fault_host_not_ready_sticky)
    );

    adaptive_aero_response_validator u_rsp (
        .clk(clk),
        .reset_n(reset_n),
        .host_resp_stream_valid(host_resp_stream_valid),
        .host_resp_stream_data(host_resp_stream_data),
        .host_resp_stream_ready(host_resp_stream_ready),
        .cfg_timeout_cycles(cfg_timeout_cycles),
        .cfg_response_seq(cfg_response_seq),
        .req_launch_pulse(req_launch_pulse),
        .rsp_packet_128(rsp_packet_128),
        .rsp_accept_pulse(rsp_accept_pulse),
        .rsp_valid_result(rsp_valid_result),
        .rsp_discard_pulse(rsp_discard_pulse),
        .rsp_match_seq(rsp_match_seq),
        .last_accepted_response_id(last_accepted_response_id),
        .discarded_response_count(discarded_response_count),
        .timeout_event_count(timeout_event_count),
        .stale_event_count(stale_event_count),
        .fault_timeout_sticky(fault_timeout_sticky),
        .fault_stale_sticky(fault_stale_sticky),
        .fault_invalid_sticky(fault_invalid_sticky)
    );

    adaptive_aero_actuator_formatter u_fmt (
        .clk(clk),
        .reset_n(reset_n),
        .cfg_clamp_min(cfg_clamp_min),
        .cfg_clamp_max(cfg_clamp_max),
        .cfg_mode_status(cfg_mode_status),
        .cfg_operating_velocity_mps(cfg_operating_velocity_mps),
        .rsp_valid_result(rsp_valid_result),
        .rsp_packet_128(rsp_packet_128),
        .act_cmd_pos(act_cmd_pos),
        .act_cmd_rate(act_cmd_rate),
        .act_cmd_enable(act_cmd_enable),
        .act_cmd_valid(act_cmd_valid),
        .act_cmd_fault_latched(act_cmd_fault_latched),
        .fallback_active(fallback_active),
        .fault_timeout_sticky(fault_timeout_sticky),
        .fault_stale_sticky(fault_stale_sticky),
        .fault_invalid_sticky(fault_invalid_sticky),
        .fault_queue_full_sticky(fault_queue_full_sticky),
        .fault_host_not_ready_sticky(fault_host_not_ready_sticky)
    );

    adaptive_aero_fault_manager u_fault (
        .clk(clk),
        .reset_n(reset_n),
        .cfg_clear_fault(cfg_clear_fault),
        .cfg_irq_enable(cfg_irq_enable),
        .rsp_accept_pulse(rsp_accept_pulse),
        .rsp_discard_pulse(rsp_discard_pulse),
        .fault_timeout_sticky(fault_timeout_sticky),
        .fault_stale_sticky(fault_stale_sticky),
        .fault_invalid_sticky(fault_invalid_sticky),
        .fault_queue_full_sticky(fault_queue_full_sticky),
        .fault_host_not_ready_sticky(fault_host_not_ready_sticky),
        .reg_request_pending(reg_request_pending),
        .cfg_fault_status(cfg_fault_status),
        .cfg_mode_status(cfg_mode_status),
        .last_fault_code(last_fault_code),
        .irq(irq)
    );

    assign host_req_stream_valid = req_fifo_push;
    assign host_req_stream_data = req_packet_128;
    assign reg_read_data = apb_ctrl_rdata;
    assign reg_read_valid = apb_ctrl_rvalid;
    assign reg_write_accept = apb_ctrl_ready;
    assign actuator_cmd_bus = {6'b0, act_cmd_valid, act_cmd_enable, act_cmd_rate, act_cmd_pos[11:0]};
assign reg_fallback_active = fallback_active;

endmodule
