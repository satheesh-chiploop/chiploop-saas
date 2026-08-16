module adaptive_aero_request_engine (
    input clk,
    input reset_n,
    input cfg_enable,
    input [2:0] cfg_mode_select,
    input cfg_pipelined_mode,
    input [15:0] cfg_nominal_stream_velocity,
    input [15:0] cfg_geometry_descriptor_id,
    input [15:0] seq_seed,
    input req_ready,
    output reg req_valid,
    output [127:0] req_data,
    output reg req_issued,
    output reg [15:0] request_seq,
    output reg request_busy,
    output reg [15:0] request_timestamp,
    output reg request_context_valid
);

reg [127:0] req_data_r;
reg [15:0] next_seq;

assign req_data = req_data_r;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        request_seq <= 16'h0000;
        request_timestamp <= 16'h0000;
        request_context_valid <= 1'b0;
        request_busy <= 1'b0;
        req_valid <= 1'b0;
        req_issued <= 1'b0;
        req_data_r <= 128'h00000000000000000000000000000000;
    end else begin
        req_issued <= 1'b0;
        if (cfg_enable && (!request_context_valid || cfg_pipelined_mode)) begin
            req_valid <= 1'b1;
            req_data_r[15:0] <= request_seq;
            req_data_r[31:16] <= cfg_nominal_stream_velocity;
            req_data_r[47:32] <= cfg_geometry_descriptor_id;
            req_data_r[50:48] <= cfg_mode_select;
            req_data_r[55:51] <= 5'b00001;
            req_data_r[71:56] <= request_timestamp;
            req_data_r[87:72] <= seq_seed;
            req_data_r[95:88] <= {3'b000, cfg_pipelined_mode, cfg_enable};
            req_data_r[111:96] <= 16'hA5A5 ^ cfg_geometry_descriptor_id ^ cfg_nominal_stream_velocity;
            req_data_r[127:112] <= 16'h5A5A ^ seq_seed ^ request_seq;
            if (req_valid && req_ready) begin
                req_issued <= 1'b1;
                request_context_valid <= 1'b1;
                request_busy <= ~cfg_pipelined_mode;
                request_timestamp <= request_timestamp + 16'h0001;
                next_seq = request_seq + 16'h0001;
                request_seq <= next_seq;
                if (!cfg_pipelined_mode) req_valid <= 1'b0;
            end
        end else begin
            req_valid <= 1'b0;
            request_busy <= request_context_valid & ~cfg_pipelined_mode;
            if (!cfg_enable) begin
                request_context_valid <= 1'b0;
                request_busy <= 1'b0;
                request_seq <= seq_seed;
                request_timestamp <= 16'h0000;
            end
        end
    end
end

endmodule
