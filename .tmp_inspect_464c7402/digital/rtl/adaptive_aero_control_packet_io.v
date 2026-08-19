module adaptive_aero_control_packet_io (
    clk,
    rst_n,
    ctrl_enable,
    ctrl_arm_output,
    ctrl_request_start,
    ctrl_bypass_model,
    seq_tx,
    timeout_cfg_cycles,
    stale_cfg_cycles,
    meta_velocity_bucket,
    meta_mode,
    meta_env_flags,
    meta_session_id,
    req_stream_data,
    req_stream_valid,
    req_stream_ready,
    rsp_stream_data,
    rsp_stream_valid,
    rsp_stream_ready,
    rsp_seq_rx,
    rsp_status,
    rsp_cmd_suggest,
    rsp_quality,
    rsp_age_echo,
    req_pending,
    rsp_seen
);

input clk;
input rst_n;
input ctrl_enable;
input ctrl_arm_output;
input ctrl_request_start;
input ctrl_bypass_model;
input [15:0] seq_tx;
input [31:0] timeout_cfg_cycles;
input [31:0] stale_cfg_cycles;
input [7:0] meta_velocity_bucket;
input [3:0] meta_mode;
input [3:0] meta_env_flags;
input [15:0] meta_session_id;
output [127:0] req_stream_data;
output req_stream_valid;
input req_stream_ready;
input [127:0] rsp_stream_data;
input rsp_stream_valid;
output rsp_stream_ready;
output [15:0] rsp_seq_rx;
output [7:0] rsp_status;
output [15:0] rsp_cmd_suggest;
output [7:0] rsp_quality;
output [15:0] rsp_age_echo;
output req_pending;
output rsp_seen;

reg [127:0] req_stream_data_r;
reg req_stream_valid_r;
reg rsp_stream_ready_r;
reg [15:0] rsp_seq_rx_r;
reg [7:0] rsp_status_r;
reg [15:0] rsp_cmd_suggest_r;
reg [7:0] rsp_quality_r;
reg [15:0] rsp_age_echo_r;
reg req_pending_r;
reg rsp_seen_r;

reg req_inflight;
reg [1:0] req_phase;
reg [15:0] req_age_ref;
reg [15:0] last_rsp_seq;
reg [127:0] req_packet;

wire req_fire;
wire rsp_fire;
wire ctrl_allow_req;
wire [15:0] timeout_lo;
wire [15:0] stale_lo;

assign req_fire = req_stream_valid_r & req_stream_ready;
assign rsp_fire = rsp_stream_valid & rsp_stream_ready_r;
assign ctrl_allow_req = ctrl_enable & ctrl_arm_output;
assign timeout_lo = timeout_cfg_cycles[15:0];
assign stale_lo = stale_cfg_cycles[15:0];

assign req_stream_data = req_stream_data_r;
assign req_stream_valid = req_stream_valid_r;
assign rsp_stream_ready = rsp_stream_ready_r;
assign rsp_seq_rx = rsp_seq_rx_r;
assign rsp_status = rsp_status_r;
assign rsp_cmd_suggest = rsp_cmd_suggest_r;
assign rsp_quality = rsp_quality_r;
assign rsp_age_echo = rsp_age_echo_r;
assign req_pending = req_pending_r;
assign rsp_seen = rsp_seen_r;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        req_stream_data_r <= 128'h00000000000000000000000000000000;
        req_stream_valid_r <= 1'b0;
        rsp_stream_ready_r <= 1'b1;
        rsp_seq_rx_r <= 16'h0000;
        rsp_status_r <= 8'h00;
        rsp_cmd_suggest_r <= 16'h0000;
        rsp_quality_r <= 8'h00;
        rsp_age_echo_r <= 16'h0000;
        req_pending_r <= 1'b0;
        rsp_seen_r <= 1'b0;
        req_inflight <= 1'b0;
        req_phase <= 2'b00;
        req_age_ref <= 16'h0000;
        last_rsp_seq <= 16'h0000;
        req_packet <= 128'h00000000000000000000000000000000;
    end else begin
        rsp_stream_ready_r <= 1'b1;
        rsp_seen_r <= 1'b0;
        if (ctrl_request_start && ctrl_allow_req && !req_inflight) begin
            req_age_ref <= req_age_ref + 16'h0001;
            req_packet <= {seq_tx, req_age_ref, timeout_lo, stale_lo, meta_session_id, 4'h0, meta_env_flags, 4'h0, meta_mode, meta_velocity_bucket, 24'h000000, ctrl_bypass_model, ctrl_arm_output, ctrl_enable, 1'b0, 47'h0000000000000};
            req_stream_data_r <= {seq_tx, req_age_ref, timeout_lo, stale_lo, meta_session_id, 4'h0, meta_env_flags, 4'h0, meta_mode, meta_velocity_bucket, 24'h000000, ctrl_bypass_model, ctrl_arm_output, ctrl_enable, 1'b0, 47'h0000000000000};
            req_stream_valid_r <= 1'b1;
            req_inflight <= 1'b1;
            req_phase <= 2'b01;
            req_pending_r <= 1'b1;
        end
        if (req_fire) begin
            req_stream_valid_r <= 1'b0;
            req_inflight <= 1'b0;
            req_phase <= 2'b10;
            req_pending_r <= 1'b0;
        end
        if (rsp_fire) begin
            rsp_seq_rx_r <= rsp_stream_data[127:112];
            rsp_status_r <= rsp_stream_data[111:104];
            rsp_cmd_suggest_r <= rsp_stream_data[103:88];
            rsp_quality_r <= rsp_stream_data[87:80];
            rsp_age_echo_r <= rsp_stream_data[79:64];
            rsp_seen_r <= 1'b1;
            last_rsp_seq <= rsp_stream_data[127:112];
        end
        if (!ctrl_allow_req) begin
            req_stream_valid_r <= 1'b0;
            req_inflight <= 1'b0;
            req_pending_r <= 1'b0;
        end
        if ((timeout_lo == 16'h0000) && ctrl_allow_req) begin
            req_phase <= req_phase;
        end
    end
end

endmodule
