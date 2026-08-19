module adaptive_aero_control_response_parser (
    clk,
    reset_n,
    stream_rsp_valid_i,
    stream_rsp_ready_o,
    stream_rsp_data_i,
    response_valid_o,
    response_id_o,
    response_sequence_o,
    response_fresh_o,
    response_drag_o,
    response_lift_o,
    response_status_flags_o,
    response_ready_pulse_o
);
input clk;
input reset_n;
input stream_rsp_valid_i;
output stream_rsp_ready_o;
input [127:0] stream_rsp_data_i;
output response_valid_o;
output [15:0] response_id_o;
output [15:0] response_sequence_o;
output response_fresh_o;
output [31:0] response_drag_o;
output [31:0] response_lift_o;
output [7:0] response_status_flags_o;
output response_ready_pulse_o;

reg stream_rsp_ready_r;
reg response_valid_r;
reg [15:0] response_id_r;
reg [15:0] response_sequence_r;
reg response_fresh_r;
reg [31:0] response_drag_r;
reg [31:0] response_lift_r;
reg [7:0] response_status_flags_r;
reg response_ready_pulse_r;
reg [127:0] rsp_word;

assign stream_rsp_ready_o = stream_rsp_ready_r;
assign response_valid_o = response_valid_r;
assign response_id_o = response_id_r;
assign response_sequence_o = response_sequence_r;
assign response_fresh_o = response_fresh_r;
assign response_drag_o = response_drag_r;
assign response_lift_o = response_lift_r;
assign response_status_flags_o = response_status_flags_r;
assign response_ready_pulse_o = response_ready_pulse_r;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        stream_rsp_ready_r <= 1'b1;
        response_valid_r <= 1'b0;
        response_id_r <= 16'h0000;
        response_sequence_r <= 16'h0000;
        response_fresh_r <= 1'b0;
        response_drag_r <= 32'h00000000;
        response_lift_r <= 32'h00000000;
        response_status_flags_r <= 8'h00;
        response_ready_pulse_r <= 1'b0;
        rsp_word <= 128'h00000000000000000000000000000000;
    end else begin
        response_ready_pulse_r <= 1'b0;
        stream_rsp_ready_r <= 1'b1;
        if (stream_rsp_valid_i && stream_rsp_ready_r) begin
            rsp_word <= stream_rsp_data_i;
            if (stream_rsp_data_i[127:120] == 8'h5A) begin
                response_valid_r <= stream_rsp_data_i[119];
                response_id_r <= stream_rsp_data_i[118:103];
                response_sequence_r <= stream_rsp_data_i[102:87];
                response_fresh_r <= stream_rsp_data_i[86];
                response_drag_r <= stream_rsp_data_i[85:54];
                response_lift_r <= stream_rsp_data_i[53:22];
                response_status_flags_r <= stream_rsp_data_i[21:14];
                response_ready_pulse_r <= 1'b1;
            end else begin
                response_valid_r <= 1'b0;
                response_ready_pulse_r <= 1'b0;
            end
        end
    end
end
endmodule
