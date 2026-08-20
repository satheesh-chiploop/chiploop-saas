module adaptive_aero_control_response_parser (
    clk,
    reset,
    rsp_data,
    rsp_valid,
    rsp_ready,
    cfg_request_sequence,
    cfg_stale_limit,
    cfg_velocity_min_mps,
    cfg_velocity_max_mps,
    response_accepted,
    response_rejected,
    response_stale,
    response_timeout,
    response_clamp_required,
    response_sequence,
    response_drag_summary,
    response_lift_summary,
    response_recommendation,
    response_metadata,
    response_checksum_ok,
    response_packet_shadow
);

input clk;
input reset;
input [127:0] rsp_data;
input rsp_valid;
output rsp_ready;
input [7:0] cfg_request_sequence;
input [7:0] cfg_stale_limit;
input [15:0] cfg_velocity_min_mps;
input [15:0] cfg_velocity_max_mps;
output response_accepted;
output response_rejected;
output response_stale;
output response_timeout;
output response_clamp_required;
output [7:0] response_sequence;
output [15:0] response_drag_summary;
output [15:0] response_lift_summary;
output [15:0] response_recommendation;
output [31:0] response_metadata;
output response_checksum_ok;
output [127:0] response_packet_shadow;
reg rsp_ready_r;
reg response_accepted_r;
reg response_rejected_r;
reg response_stale_r;
reg response_timeout_r;
reg response_clamp_required_r;
reg [7:0] response_sequence_r;
reg [15:0] response_drag_summary_r;
reg [15:0] response_lift_summary_r;
reg [15:0] response_recommendation_r;
reg [31:0] response_metadata_r;
reg response_checksum_ok_r;
reg [127:0] response_packet_shadow_r;
wire [7:0] rsp_version;
wire [7:0] rsp_sequence;
wire [15:0] rsp_drag;
wire [15:0] rsp_lift;
wire [15:0] rsp_recommend;
wire [15:0] rsp_age;
wire [7:0] rsp_checksum;
wire [7:0] calc_checksum;
wire checksum_ok;
wire seq_ok;
wire version_ok;
wire stale_ok;
wire range_ok;
wire accepted;

assign rsp_version = rsp_data[127:120];
assign rsp_sequence = rsp_data[111:104];
assign rsp_age = rsp_data[103:88];
assign rsp_drag = rsp_data[87:72];
assign rsp_lift = rsp_data[71:56];
assign rsp_recommend = rsp_data[55:40];
assign rsp_checksum = rsp_data[7:0];
assign calc_checksum = rsp_data[127:120] ^ rsp_data[119:112] ^ rsp_data[111:104] ^ rsp_data[103:96] ^ rsp_data[95:88] ^ rsp_data[87:80] ^ rsp_data[79:72] ^ rsp_data[71:64] ^ rsp_data[63:56] ^ rsp_data[55:48] ^ rsp_data[47:40] ^ rsp_data[39:32] ^ rsp_data[31:24] ^ rsp_data[23:16] ^ rsp_data[15:8];
assign checksum_ok = (calc_checksum == rsp_checksum);
assign version_ok = (rsp_version == 8'h01);
assign seq_ok = (rsp_sequence == cfg_request_sequence);
assign stale_ok = (rsp_age <= {8'h00, cfg_stale_limit});
assign range_ok = (rsp_drag >= cfg_velocity_min_mps) & (rsp_drag <= cfg_velocity_max_mps) & (rsp_lift >= cfg_velocity_min_mps) & (rsp_lift <= cfg_velocity_max_mps);
assign accepted = rsp_valid & checksum_ok & version_ok & seq_ok & stale_ok & range_ok;

always @(posedge clk) begin
    if (reset) begin
        rsp_ready_r <= 1'b1;
        response_accepted_r <= 1'b0;
        response_rejected_r <= 1'b0;
        response_stale_r <= 1'b0;
        response_timeout_r <= 1'b0;
        response_clamp_required_r <= 1'b0;
        response_sequence_r <= 8'h00;
        response_drag_summary_r <= 16'h0000;
        response_lift_summary_r <= 16'h0000;
        response_recommendation_r <= 16'h0000;
        response_metadata_r <= 32'h00000000;
        response_checksum_ok_r <= 1'b0;
        response_packet_shadow_r <= 128'h00000000000000000000000000000000;
    end else begin
        rsp_ready_r <= 1'b1;
        response_accepted_r <= 1'b0;
        response_rejected_r <= 1'b0;
        response_stale_r <= 1'b0;
        response_timeout_r <= 1'b0;
        response_clamp_required_r <= 1'b0;
        response_checksum_ok_r <= checksum_ok;
        if (rsp_valid) begin
            response_packet_shadow_r <= rsp_data;
            response_sequence_r <= rsp_sequence;
            if (accepted) begin
                response_accepted_r <= 1'b1;
                response_drag_summary_r <= rsp_drag;
                response_lift_summary_r <= rsp_lift;
                response_recommendation_r <= rsp_recommend;
                response_metadata_r <= {rsp_version, rsp_sequence, rsp_age[7:0], rsp_checksum};
                response_clamp_required_r <= ((rsp_recommend < cfg_velocity_min_mps[15:0]) | (rsp_recommend > cfg_velocity_max_mps[15:0]) | (rsp_drag < cfg_velocity_min_mps[15:0]) | (rsp_drag > cfg_velocity_max_mps[15:0]) | (rsp_lift < cfg_velocity_min_mps[15:0]) | (rsp_lift > cfg_velocity_max_mps[15:0]));
            end else begin
                response_rejected_r <= 1'b1;
                response_stale_r <= ~stale_ok;
                response_timeout_r <= ~version_ok | ~checksum_ok;
            end
        end
    end
end

assign rsp_ready = rsp_ready_r;
assign response_accepted = response_accepted_r;
assign response_rejected = response_rejected_r;
assign response_stale = response_stale_r;
assign response_timeout = response_timeout_r;
assign response_clamp_required = response_clamp_required_r;
assign response_sequence = response_sequence_r;
assign response_drag_summary = response_drag_summary_r;
assign response_lift_summary = response_lift_summary_r;
assign response_recommendation = response_recommendation_r;
assign response_metadata = response_metadata_r;
assign response_checksum_ok = response_checksum_ok_r;
assign response_packet_shadow = response_packet_shadow_r;

endmodule
