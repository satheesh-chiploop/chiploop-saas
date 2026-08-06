module telemetry_monitor (
    input         clk,
    input         rst_n,
    input         accepted_response_pulse,
    input         rejected_stale_pulse,
    input         clamp_event_pulse,
    input         timeout_event_pulse,
    input         fallback_activation_pulse,
    input         sticky_clear_in,
    output [31:0] accepted_response_count_out,
    output [31:0] rejected_stale_count_out,
    output [31:0] clamp_event_count_out,
    output [31:0] timeout_event_count_out,
    output [31:0] fallback_activation_count_out,
    input  [7:0] sticky_status_out
);
    reg [31:0] accepted_response_count_r;
    reg [31:0] rejected_stale_count_r;
    reg [31:0] clamp_event_count_r;
    reg [31:0] timeout_event_count_r;
    reg [31:0] fallback_activation_count_r;
    assign accepted_response_count_out = accepted_response_count_r;
    assign rejected_stale_count_out = rejected_stale_count_r;
    assign clamp_event_count_out = clamp_event_count_r;
    assign timeout_event_count_out = timeout_event_count_r;
    assign fallback_activation_count_out = fallback_activation_count_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            accepted_response_count_r <= 32'h0000_0000;
            rejected_stale_count_r <= 32'h0000_0000;
            clamp_event_count_r <= 32'h0000_0000;
            timeout_event_count_r <= 32'h0000_0000;
            fallback_activation_count_r <= 32'h0000_0000;
        end else begin
            accepted_response_count_r <= accepted_response_count_r + {31'h0, accepted_response_pulse};
            rejected_stale_count_r <= rejected_stale_count_r + {31'h0, rejected_stale_pulse};
            clamp_event_count_r <= clamp_event_count_r + {31'h0, clamp_event_pulse};
            timeout_event_count_r <= timeout_event_count_r + {31'h0, timeout_event_pulse};
            fallback_activation_count_r <= fallback_activation_count_r + {31'h0, fallback_activation_pulse};
            if (sticky_clear_in) begin
                accepted_response_count_r <= accepted_response_count_r;
                rejected_stale_count_r <= rejected_stale_count_r;
                clamp_event_count_r <= clamp_event_count_r;
                timeout_event_count_r <= timeout_event_count_r;
                fallback_activation_count_r <= fallback_activation_count_r;
            end
        end
    end
endmodule
