module adaptive_aero_control_validator (
    clk,
    rst_n,
    enable,
    mode_select,
    max_cmd,
    min_cmd,
    rate_limit,
    fallback_mode,
    rsp_accepted,
    rsp_seq,
    rsp_age_tag,
    rsp_metadata,
    rsp_handle,
    rsp_malformed,
    rsp_stale,
    rsp_seq_mismatch,
    rsp_duplicate,
    outstanding_timer_expired,
    transport_fault,
    candidate_cmd,
    candidate_valid,
    candidate_fallback,
    candidate_invalid,
    cmd_bounded,
    cmd_valid,
    cmd_clamped_low,
    cmd_clamped_high,
    rate_limited,
    service_unavailable,
    fallback_selected
);
    input clk;
    input rst_n;
    input enable;
    input [2:0] mode_select;
    input [15:0] max_cmd;
    input [15:0] min_cmd;
    input [15:0] rate_limit;
    input [3:0] fallback_mode;
    input rsp_accepted;
    input [15:0] rsp_seq;
    input [7:0] rsp_age_tag;
    input [31:0] rsp_metadata;
    input [15:0] rsp_handle;
    input rsp_malformed;
    input rsp_stale;
    input rsp_seq_mismatch;
    input rsp_duplicate;
    input outstanding_timer_expired;
    input transport_fault;
    output [15:0] candidate_cmd;
    output candidate_valid;
    output candidate_fallback;
    output candidate_invalid;
    output [15:0] cmd_bounded;
    output cmd_valid;
    output cmd_clamped_low;
    output cmd_clamped_high;
    output rate_limited;
    output service_unavailable;
    output fallback_selected;

    reg [15:0] candidate_cmd_r;
    reg candidate_valid_r;
    reg candidate_fallback_r;
    reg candidate_invalid_r;
    reg [15:0] cmd_bounded_r;
    reg cmd_valid_r;
    reg cmd_clamped_low_r;
    reg cmd_clamped_high_r;
    reg rate_limited_r;
    reg service_unavailable_r;
    reg fallback_selected_r;
    reg [15:0] last_cmd_r;

    wire [15:0] raw_candidate;
    assign raw_candidate = rsp_metadata[15:0] ^ rsp_handle ^ {8'h00, rsp_age_tag} ^ rsp_seq ^ {13'b0, mode_select};

    assign candidate_cmd = candidate_cmd_r;
    assign candidate_valid = candidate_valid_r;
    assign candidate_fallback = candidate_fallback_r;
    assign candidate_invalid = candidate_invalid_r;
    assign cmd_bounded = cmd_bounded_r;
    assign cmd_valid = cmd_valid_r;
    assign cmd_clamped_low = cmd_clamped_low_r;
    assign cmd_clamped_high = cmd_clamped_high_r;
    assign rate_limited = rate_limited_r;
    assign service_unavailable = service_unavailable_r;
    assign fallback_selected = fallback_selected_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            candidate_cmd_r <= 16'h0000;
            candidate_valid_r <= 1'b0;
            candidate_fallback_r <= 1'b1;
            candidate_invalid_r <= 1'b0;
            cmd_bounded_r <= 16'h0000;
            cmd_valid_r <= 1'b0;
            cmd_clamped_low_r <= 1'b0;
            cmd_clamped_high_r <= 1'b0;
            rate_limited_r <= 1'b0;
            service_unavailable_r <= 1'b1;
            fallback_selected_r <= 1'b1;
            last_cmd_r <= 16'h0000;
        end else begin
            candidate_valid_r <= 1'b0;
            candidate_fallback_r <= 1'b0;
            candidate_invalid_r <= 1'b0;
            cmd_valid_r <= 1'b0;
            cmd_clamped_low_r <= 1'b0;
            cmd_clamped_high_r <= 1'b0;
            rate_limited_r <= 1'b0;
            service_unavailable_r <= 1'b0;
            fallback_selected_r <= 1'b0;

            if (!enable || rsp_malformed || rsp_stale || rsp_seq_mismatch || rsp_duplicate || outstanding_timer_expired || transport_fault) begin
                candidate_cmd_r <= {12'h000, fallback_mode};
                candidate_fallback_r <= 1'b1;
                candidate_invalid_r <= 1'b1;
                cmd_bounded_r <= {12'h000, fallback_mode};
                cmd_valid_r <= 1'b1;
                service_unavailable_r <= 1'b1;
                fallback_selected_r <= 1'b1;
                candidate_cmd_r <= {12'h000, fallback_mode};
            end else if (rsp_accepted) begin
                candidate_cmd_r <= raw_candidate;
                candidate_valid_r <= 1'b1;
                if (raw_candidate > max_cmd) begin
                    cmd_bounded_r <= max_cmd;
                    cmd_clamped_high_r <= 1'b1;
                end else if (raw_candidate < min_cmd) begin
                    cmd_bounded_r <= min_cmd;
                    cmd_clamped_low_r <= 1'b1;
                end else begin
                    cmd_bounded_r <= raw_candidate;
                end
                if (rate_limit != 16'h0000) begin
                    if (raw_candidate > (last_cmd_r + rate_limit)) begin
                        cmd_bounded_r <= last_cmd_r + rate_limit;
                        rate_limited_r <= 1'b1;
                    end else if (raw_candidate < (last_cmd_r - rate_limit)) begin
                        cmd_bounded_r <= last_cmd_r - rate_limit;
                        rate_limited_r <= 1'b1;
                    end
                end
                cmd_valid_r <= 1'b1;
                last_cmd_r <= cmd_bounded_r;
            end else begin
                candidate_cmd_r <= {12'h000, fallback_mode};
                candidate_fallback_r <= 1'b1;
                cmd_bounded_r <= {12'h000, fallback_mode};
                service_unavailable_r <= 1'b1;
                fallback_selected_r <= 1'b1;
            end
        end
    end
endmodule
