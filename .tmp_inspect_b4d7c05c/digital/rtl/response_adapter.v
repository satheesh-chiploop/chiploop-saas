module response_adapter (
    clk,
    reset_n,
    rsp_valid,
    rsp_ready,
    rsp_payload,
    busy,
    expected_seq,
    freshness_ok,
    timeout_expired,
    response_seq,
    drag_estimate,
    lift_estimate,
    confidence_flags,
    diagnostic_code,
    response_valid,
    response_seq_mismatch,
    stale_fault,
    invalid_payload_fault
);
    input clk;
    input reset_n;
    input rsp_valid;
    output rsp_ready;
    input [127:0] rsp_payload;
    input busy;
    input [15:0] expected_seq;
    input freshness_ok;
    input timeout_expired;
    output [15:0] response_seq;
    output [31:0] drag_estimate;
    output [31:0] lift_estimate;
    output [7:0] confidence_flags;
    output [7:0] diagnostic_code;
    output response_valid;
    output response_seq_mismatch;
    output stale_fault;
    output invalid_payload_fault;

    reg rsp_ready_r;
    reg [15:0] response_seq_r;
    reg [31:0] drag_estimate_r;
    reg [31:0] lift_estimate_r;
    reg [7:0] confidence_flags_r;
    reg [7:0] diagnostic_code_r;
    reg response_valid_r;
    reg response_seq_mismatch_r;
    reg stale_fault_r;
    reg invalid_payload_fault_r;

    assign rsp_ready = rsp_ready_r;
    assign response_seq = response_seq_r;
    assign drag_estimate = drag_estimate_r;
    assign lift_estimate = lift_estimate_r;
    assign confidence_flags = confidence_flags_r;
    assign diagnostic_code = diagnostic_code_r;
    assign response_valid = response_valid_r;
    assign response_seq_mismatch = response_seq_mismatch_r;
    assign stale_fault = stale_fault_r;
    assign invalid_payload_fault = invalid_payload_fault_r;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            rsp_ready_r <= 1'b0;
            response_seq_r <= 16'h0000;
            drag_estimate_r <= 32'h00000000;
            lift_estimate_r <= 32'h00000000;
            confidence_flags_r <= 8'h00;
            diagnostic_code_r <= 8'h00;
            response_valid_r <= 1'b0;
            response_seq_mismatch_r <= 1'b0;
            stale_fault_r <= 1'b0;
            invalid_payload_fault_r <= 1'b0;
        end else begin
            rsp_ready_r <= busy & !timeout_expired & freshness_ok;
            response_valid_r <= 1'b0;
            response_seq_mismatch_r <= 1'b0;
            stale_fault_r <= 1'b0;
            invalid_payload_fault_r <= 1'b0;
            if (rsp_valid && rsp_ready_r) begin
                if (timeout_expired || !freshness_ok) begin
                    stale_fault_r <= 1'b1;
                end else if (rsp_payload[15:0] != expected_seq) begin
                    response_seq_mismatch_r <= 1'b1;
                end else begin
                    response_seq_r <= rsp_payload[15:0];
                    drag_estimate_r <= rsp_payload[47:16];
                    lift_estimate_r <= rsp_payload[79:48];
                    confidence_flags_r <= rsp_payload[87:80];
                    diagnostic_code_r <= rsp_payload[95:88];
                    if (rsp_payload[95:88] != 8'h00 && rsp_payload[87:80] == 8'h00) begin
                        invalid_payload_fault_r <= 1'b1;
                    end else begin
                        response_valid_r <= 1'b1;
                    end
                end
            end
        end
    end

endmodule
