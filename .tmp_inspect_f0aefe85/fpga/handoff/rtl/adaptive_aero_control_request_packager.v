module adaptive_aero_control_request_packager (
    clk,
    reset,
    cfg_enable,
    cfg_mode_select,
    cfg_request_sequence,
    cfg_velocity_mps,
    cfg_velocity_min_mps,
    cfg_velocity_max_mps,
    request_packet,
    request_valid,
    request_ready,
    request_coherent,
    request_packet_shadow
);

input clk;
input reset;
input cfg_enable;
input [2:0] cfg_mode_select;
input [7:0] cfg_request_sequence;
input [15:0] cfg_velocity_mps;
input [15:0] cfg_velocity_min_mps;
input [15:0] cfg_velocity_max_mps;
output [127:0] request_packet;
output request_valid;
input request_ready;
input request_coherent;
output [127:0] request_packet_shadow;
reg [127:0] request_packet_r;
reg request_valid_r;
reg [15:0] age_ctr;
reg [7:0] seq_latched;
reg [15:0] velocity_latched;
reg [2:0] mode_latched;

wire coherent;
assign coherent = cfg_enable & request_coherent & (cfg_velocity_mps >= cfg_velocity_min_mps) & (cfg_velocity_mps <= cfg_velocity_max_mps);

always @(posedge clk) begin
    if (reset) begin
        request_packet_r <= 128'h00000000000000000000000000000000;
        request_valid_r <= 1'b0;
        age_ctr <= 16'h0000;
        seq_latched <= 8'h00;
        velocity_latched <= 16'h0000;
        mode_latched <= 3'b000;
    end else begin
        if (coherent && request_ready) begin
            seq_latched <= cfg_request_sequence;
            velocity_latched <= cfg_velocity_mps;
            mode_latched <= cfg_mode_select;
            age_ctr <= age_ctr + 16'h0001;
            request_packet_r <= {8'hA5, 8'h01, cfg_request_sequence, age_ctr[7:0], cfg_velocity_mps, cfg_velocity_min_mps, cfg_velocity_max_mps, 16'h0000, 8'h00, cfg_mode_select, 21'b0};
            request_valid_r <= 1'b1;
        end else if (request_valid_r && request_ready) begin
            request_valid_r <= 1'b0;
        end else if (!coherent) begin
            request_valid_r <= 1'b0;
        end
        request_packet_r[31:0] <= {cfg_mode_select, cfg_request_sequence, cfg_velocity_mps[7:0], cfg_velocity_mps[15:8], age_ctr[7:0], age_ctr[15:8], 8'h00, 8'h5A};
    end
end

assign request_packet = request_packet_r;
assign request_valid = request_valid_r;
assign request_packet_shadow = request_packet_r;

endmodule
