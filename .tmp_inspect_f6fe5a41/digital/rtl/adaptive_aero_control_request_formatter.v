module adaptive_aero_control_request_formatter (
    clk,
    reset_n,
    cfg_enable_i,
    cfg_arm_i,
    cfg_mode_i,
    cfg_velocity_setpoint_i,
    cfg_sequence_counter_i,
    req_due_i,
    local_timestamp_i,
    request_id_i,
    stream_req_ready_i,
    stream_req_valid_o,
    stream_req_data_o,
    request_issued_o,
    request_sequence_o
);
input clk;
input reset_n;
input cfg_enable_i;
input cfg_arm_i;
input [1:0] cfg_mode_i;
input [31:0] cfg_velocity_setpoint_i;
input [15:0] cfg_sequence_counter_i;
input req_due_i;
input [31:0] local_timestamp_i;
input [15:0] request_id_i;
input stream_req_ready_i;
output stream_req_valid_o;
output [127:0] stream_req_data_o;
output request_issued_o;
output [15:0] request_sequence_o;
reg stream_req_valid_r;
reg [127:0] stream_req_data_r;
reg request_issued_r;
reg [15:0] request_sequence_r;
reg [1:0] req_state;
reg [31:0] timestamp_latched;
localparam REQ_IDLE = 2'b00;
localparam REQ_WAIT = 2'b01;
localparam REQ_SEND = 2'b10;

assign stream_req_valid_o = stream_req_valid_r;
assign stream_req_data_o = stream_req_data_r;
assign request_issued_o = request_issued_r;
assign request_sequence_o = request_sequence_r;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        stream_req_valid_r <= 1'b0;
        stream_req_data_r <= 128'h00000000000000000000000000000000;
        request_issued_r <= 1'b0;
        request_sequence_r <= 16'h0000;
        req_state <= REQ_IDLE;
        timestamp_latched <= 32'h00000000;
    end else begin
        request_issued_r <= 1'b0;
        case (req_state)
            REQ_IDLE: begin
                if (cfg_enable_i & cfg_arm_i & req_due_i) begin
                    timestamp_latched <= local_timestamp_i;
                    stream_req_data_r <= {16'hA55A, request_id_i, cfg_sequence_counter_i, local_timestamp_i, cfg_velocity_setpoint_i, 8'h00, cfg_mode_i, 6'b0};
                    stream_req_valid_r <= 1'b1;
                    request_sequence_r <= cfg_sequence_counter_i;
                    req_state <= REQ_WAIT;
                end else begin
                    stream_req_valid_r <= 1'b0;
                end
            end
            REQ_WAIT: begin
                stream_req_valid_r <= 1'b1;
                if (stream_req_ready_i) begin
                    request_issued_r <= 1'b1;
                    stream_req_valid_r <= 1'b0;
                    req_state <= REQ_IDLE;
                end
            end
            default: begin
                req_state <= REQ_IDLE;
                stream_req_valid_r <= 1'b0;
            end
        endcase
    end
end
endmodule
