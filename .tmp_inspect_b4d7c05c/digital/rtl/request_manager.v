module request_manager (
    clk,
    reset_n,
    start_request,
    clear_faults,
    request_seq,
    stream_velocity,
    geometry_id,
    flow_condition_sel,
    control_mode,
    config_valid,
    busy,
    req_payload,
    req_valid,
    req_ready,
    req_issued,
    request_seq_latched,
    request_invalid,
    timeout_expired,
    fault_latched
);
    input clk;
    input reset_n;
    input start_request;
    input clear_faults;
    input [15:0] request_seq;
    input [31:0] stream_velocity;
    input [15:0] geometry_id;
    input [3:0] flow_condition_sel;
    input [3:0] control_mode;
    input config_valid;
    output busy;
    output [127:0] req_payload;
    output req_valid;
    input req_ready;
    output req_issued;
    output [15:0] request_seq_latched;
    output request_invalid;
    input timeout_expired;
    input fault_latched;

    reg busy_r;
    reg [127:0] req_payload_r;
    reg req_valid_r;
    reg req_issued_r;
    reg [15:0] request_seq_latched_r;
    reg request_invalid_r;

    assign busy = busy_r;
    assign req_payload = req_payload_r;
    assign req_valid = req_valid_r;
    assign req_issued = req_issued_r;
    assign request_seq_latched = request_seq_latched_r;
    assign request_invalid = request_invalid_r;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            busy_r <= 1'b0;
            req_payload_r <= 128'h00000000000000000000000000000000;
            req_valid_r <= 1'b0;
            req_issued_r <= 1'b0;
            request_seq_latched_r <= 16'h0000;
            request_invalid_r <= 1'b0;
        end else begin
            req_issued_r <= 1'b0;
            request_invalid_r <= 1'b0;
            if (clear_faults) begin
                request_invalid_r <= 1'b0;
            end
            if (req_valid_r && req_ready) begin
                req_valid_r <= 1'b0;
                busy_r <= 1'b0;
            end
            if (timeout_expired || fault_latched) begin
                busy_r <= busy_r;
            end
            if (start_request && !busy_r) begin
                if (config_valid) begin
                    request_seq_latched_r <= request_seq;
                    req_payload_r <= {16'b0, 32'h00000000, 8'h00, control_mode, flow_condition_sel, geometry_id, stream_velocity, request_seq};
                    req_valid_r <= 1'b1;
                    busy_r <= 1'b1;
                    req_issued_r <= 1'b1;
                end else begin
                    request_invalid_r <= 1'b1;
                    busy_r <= 1'b0;
                    req_valid_r <= 1'b0;
                end
            end
            if (clear_faults && !busy_r) begin
                request_invalid_r <= 1'b0;
            end
        end
    end

endmodule
