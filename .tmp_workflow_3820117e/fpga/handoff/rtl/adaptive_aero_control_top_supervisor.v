module adaptive_aero_control_top_supervisor (
    clk,
    rst_n,
    cfg_enable,
    cfg_safe_fallback_select,
    cfg_max_cmd_pos,
    cfg_min_cmd_pos,
    cfg_max_cmd_rate,
    cfg_stale_timeout_cycles,
    cfg_response_timeout_cycles,
    cfg_sequence_expected,
    cfg_stream_velocity_setpoint,
    cfg_fault_mask,
    model_req_ready,
    model_rsp_valid,
    model_rsp_data,
    model_req_valid,
    model_req_data,
    model_rsp_ready,
    external_fault_i,
    actuator_out_valid,
    actuator_out_cmd,
    status_busy_o,
    status_accepted_o,
    status_rejected_stale_o,
    status_rejected_seq_o,
    status_timeout_o,
    status_fallback_active_o,
    status_clamped_o,
    status_fault_summary_o
);

input clk;
input rst_n;
input cfg_enable;
input cfg_safe_fallback_select;
input [63:0] cfg_max_cmd_pos;
input [63:0] cfg_min_cmd_pos;
input [63:0] cfg_max_cmd_rate;
input [63:0] cfg_stale_timeout_cycles;
input [63:0] cfg_response_timeout_cycles;
input [63:0] cfg_sequence_expected;
input [63:0] cfg_stream_velocity_setpoint;
input [63:0] cfg_fault_mask;
input model_req_ready;
input model_rsp_valid;
input [63:0] model_rsp_data;
output model_req_valid;
output [63:0] model_req_data;
output model_rsp_ready;
input external_fault_i;
output actuator_out_valid;
output [63:0] actuator_out_cmd;
output status_busy_o;
output status_accepted_o;
output status_rejected_stale_o;
output status_rejected_seq_o;
output status_timeout_o;
output status_fallback_active_o;
output status_clamped_o;
output status_fault_summary_o;

localparam ST_IDLE = 3'd0;
localparam ST_CAPTURE = 3'd1;
localparam ST_VALIDATE = 3'd2;
localparam ST_WAIT_RESP = 3'd3;
localparam ST_ISSUE_CMD = 3'd4;
localparam ST_CLAMP_CMD = 3'd5;
localparam ST_REPORT = 3'd6;

reg [2:0] state_r;
reg [2:0] state_n;
reg model_req_valid_r;
reg [63:0] model_req_data_r;
reg model_rsp_ready_r;
reg actuator_out_valid_r;
reg [63:0] actuator_out_cmd_r;
reg status_busy_r;
reg status_accepted_r;
reg status_rejected_stale_r;
reg status_rejected_seq_r;
reg status_timeout_r;
reg status_fallback_active_r;
reg status_clamped_r;
reg status_fault_summary_r;

reg [63:0] age_cnt_r;
reg [63:0] resp_cnt_r;
reg [63:0] seq_latched_r;
reg [63:0] cmd_latched_r;
reg [63:0] clamped_cmd_r;

wire signed [63:0] rsp_cmd_s;
wire signed [63:0] min_cmd_s;
wire signed [63:0] max_cmd_s;
wire signed [63:0] raw_cmd_s;
wire signed [63:0] clamped_low_s;
wire signed [63:0] clamped_high_s;
wire seq_match;
wire stale_hit;
wire timeout_hit;
wire fault_hit;
wire clamp_hit;
wire enable_ok;
wire req_accept_ok;

assign model_req_valid = model_req_valid_r;
assign model_req_data = model_req_data_r;
assign model_rsp_ready = model_rsp_ready_r;
assign actuator_out_valid = actuator_out_valid_r;
assign actuator_out_cmd = actuator_out_cmd_r;
assign status_busy_o = status_busy_r;
assign status_accepted_o = status_accepted_r;
assign status_rejected_stale_o = status_rejected_stale_r;
assign status_rejected_seq_o = status_rejected_seq_r;
assign status_timeout_o = status_timeout_r;
assign status_fallback_active_o = status_fallback_active_r;
assign status_clamped_o = status_clamped_r;
assign status_fault_summary_o = status_fault_summary_r;

assign rsp_cmd_s = $signed(model_rsp_data);
assign min_cmd_s = $signed(cfg_min_cmd_pos);
assign max_cmd_s = $signed(cfg_max_cmd_pos);
assign raw_cmd_s = $signed(model_rsp_data);
assign clamped_low_s = (raw_cmd_s < min_cmd_s) ? min_cmd_s : raw_cmd_s;
assign clamped_high_s = (clamped_low_s > max_cmd_s) ? max_cmd_s : clamped_low_s;
assign seq_match = (cfg_sequence_expected == seq_latched_r);
assign stale_hit = (cfg_stale_timeout_cycles != 64'h0000000000000000) && (age_cnt_r >= cfg_stale_timeout_cycles);
assign timeout_hit = (cfg_response_timeout_cycles != 64'h0000000000000000) && (resp_cnt_r >= cfg_response_timeout_cycles);
assign fault_hit = external_fault_i | timeout_hit | stale_hit | (~enable_ok) | (~seq_match);
assign clamp_hit = (clamped_high_s != raw_cmd_s);
assign enable_ok = cfg_enable;
assign req_accept_ok = enable_ok && seq_match && (~stale_hit) && (~external_fault_i);

always @(*) begin
    state_n = state_r;
    model_req_valid_r = 1'b0;
    model_req_data_r = 64'h0000000000000000;
    model_rsp_ready_r = 1'b0;
    status_busy_r = 1'b0;
    status_clamped_r = 1'b0;

    case (state_r)
        ST_IDLE: begin
            if (cfg_enable && !external_fault_i) begin
                state_n = ST_CAPTURE;
            end
        end
        ST_CAPTURE: begin
            model_req_valid_r = 1'b1;
            model_req_data_r = {cfg_stream_velocity_setpoint[31:0], cfg_sequence_expected[31:0]};
            if (model_req_ready) begin
                state_n = ST_VALIDATE;
            end
        end
        ST_VALIDATE: begin
            if (!cfg_enable) begin
                state_n = ST_REPORT;
            end else if (external_fault_i) begin
                state_n = ST_REPORT;
            end else if (cfg_sequence_expected != seq_latched_r) begin
                state_n = ST_REPORT;
            end else if (stale_hit) begin
                state_n = ST_REPORT;
            end else begin
                state_n = ST_WAIT_RESP;
            end
        end
        ST_WAIT_RESP: begin
            status_busy_r = 1'b1;
            model_rsp_ready_r = 1'b1;
            if (model_rsp_valid) begin
                state_n = ST_ISSUE_CMD;
            end else if (timeout_hit) begin
                state_n = ST_REPORT;
            end
        end
        ST_ISSUE_CMD: begin
            status_busy_r = 1'b1;
            if (clamp_hit) begin
                state_n = ST_CLAMP_CMD;
            end else begin
                state_n = ST_REPORT;
            end
        end
        ST_CLAMP_CMD: begin
            status_busy_r = 1'b1;
            status_clamped_r = 1'b1;
            state_n = ST_REPORT;
        end
        ST_REPORT: begin
            status_busy_r = 1'b0;
            if (req_accept_ok && model_rsp_valid && !timeout_hit && !external_fault_i && !stale_hit) begin
            end
            state_n = ST_IDLE;
        end
        default: begin
            state_n = ST_IDLE;
        end
    endcase
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state_r <= ST_IDLE;
        actuator_out_valid_r <= 1'b0;
        actuator_out_cmd_r <= 64'h0000000000000000;
        status_accepted_r <= 1'b0;
        status_fallback_active_r <= 1'b0;
        status_fault_summary_r <= 1'b0;
        age_cnt_r <= 64'h0000000000000000;
        resp_cnt_r <= 64'h0000000000000000;
        seq_latched_r <= 64'h0000000000000000;
        cmd_latched_r <= 64'h0000000000000000;
        clamped_cmd_r <= 64'h0000000000000000;
    end else begin
        state_r <= state_n;
        status_accepted_r <= 1'b0;
        if (cfg_enable) begin
            if (age_cnt_r != 64'hffffffffffffffff) age_cnt_r <= age_cnt_r + 64'h0000000000000001;
        end else begin
            age_cnt_r <= 64'h0000000000000000;
        end
        if (state_r == ST_WAIT_RESP) begin
            if (resp_cnt_r != 64'hffffffffffffffff) resp_cnt_r <= resp_cnt_r + 64'h0000000000000001;
        end else begin
            resp_cnt_r <= 64'h0000000000000000;
        end
        if (state_r == ST_CAPTURE) begin
            seq_latched_r <= cfg_sequence_expected;
            cmd_latched_r <= model_rsp_data;
        end
        if (state_r == ST_ISSUE_CMD || state_r == ST_CLAMP_CMD || state_r == ST_REPORT) begin
            clamped_cmd_r <= clamped_high_s;
        end
        if (state_r == ST_REPORT) begin
            if (req_accept_ok && model_rsp_valid && !timeout_hit && !external_fault_i && !stale_hit) begin
                status_accepted_r <= 1'b1;
                actuator_out_valid_r <= 1'b1;
                actuator_out_cmd_r <= clamped_high_s;
            end else begin
                actuator_out_valid_r <= 1'b0;
                actuator_out_cmd_r <= 64'h0000000000000000;
            end
            status_fallback_active_r <= fault_hit;
            status_fault_summary_r <= fault_hit;
            if (stale_hit) status_rejected_stale_r <= 1'b1;
            if ((~seq_match) || (~cfg_enable)) status_rejected_seq_r <= 1'b1;
            if (timeout_hit) status_timeout_r <= 1'b1;
        end else if (external_fault_i || timeout_hit || stale_hit || (~cfg_enable)) begin
            actuator_out_valid_r <= 1'b0;
            actuator_out_cmd_r <= 64'h0000000000000000;
            status_fallback_active_r <= 1'b1;
            status_fault_summary_r <= 1'b1;
        end
    end
end

endmodule
