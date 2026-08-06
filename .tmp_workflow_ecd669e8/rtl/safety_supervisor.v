module safety_supervisor (
    input         clk,
    input         rst_n,
    input         envelope_violation_in,
    input         response_stale_in,
    input         response_invalid_in,
    input         response_timeout_in,
    input         clamp_active_in,
    input         command_out_of_bounds_in,
    input         internal_fault_in,
    input         host_clear_sticky,
    output        stale_reject_out,
    output        timeout_fault_out,
    output        invalid_response_out,
    output        clamp_active_out,
    output        fallback_active_out,
    output [7:0] safety_status_out,
    output [7:0] sticky_status_out
);
    reg [7:0] safety_status_r;
    reg [7:0] sticky_status_r;
    reg stale_reject_r;
    reg timeout_fault_r;
    reg invalid_response_r;
    reg clamp_active_r;
    reg fallback_active_r;

    assign stale_reject_out = stale_reject_r;
    assign timeout_fault_out = timeout_fault_r;
    assign invalid_response_out = invalid_response_r;
    assign clamp_active_out = clamp_active_r;
    assign fallback_active_out = fallback_active_r;
    assign safety_status_out = safety_status_r;
    assign sticky_status_out = sticky_status_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            safety_status_r <= 8'h10;
            sticky_status_r <= 8'h10;
            stale_reject_r <= 1'b0;
            timeout_fault_r <= 1'b0;
            invalid_response_r <= 1'b0;
            clamp_active_r <= 1'b0;
            fallback_active_r <= 1'b1;
        end else begin
            stale_reject_r <= response_stale_in;
            timeout_fault_r <= response_timeout_in;
            invalid_response_r <= response_invalid_in;
            clamp_active_r <= clamp_active_in;
            fallback_active_r <= envelope_violation_in | response_stale_in | response_invalid_in | response_timeout_in | clamp_active_in | command_out_of_bounds_in | internal_fault_in;
            safety_status_r[0] <= response_stale_in;
            safety_status_r[1] <= response_timeout_in;
            safety_status_r[2] <= response_invalid_in;
            safety_status_r[3] <= clamp_active_in;
            safety_status_r[4] <= fallback_active_r;
            safety_status_r[5] <= envelope_violation_in;
            safety_status_r[6] <= internal_fault_in;
            safety_status_r[7] <= 1'b0;
            if (host_clear_sticky) begin
                sticky_status_r <= 8'h00;
            end else begin
                sticky_status_r[0] <= response_stale_in | sticky_status_r[0];
                sticky_status_r[1] <= response_timeout_in | sticky_status_r[1];
                sticky_status_r[2] <= response_invalid_in | sticky_status_r[2];
                sticky_status_r[3] <= clamp_active_in | sticky_status_r[3];
                sticky_status_r[4] <= fallback_active_r | sticky_status_r[4];
                sticky_status_r[5] <= envelope_violation_in | sticky_status_r[5];
                sticky_status_r[6] <= internal_fault_in | sticky_status_r[6];
                sticky_status_r[7] <= 1'b0;
            end
        end
    end
endmodule
