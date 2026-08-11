module adaptive_aero_control_transport (
    clk,
    rst_n,
    enable,
    mode_select,
    freshness_limit,
    timeout_limit,
    sequence_counter,
    req_stream_valid,
    req_stream_ready,
    req_stream_data,
    rsp_stream_valid,
    rsp_stream_ready,
    rsp_stream_data,
    req_issued,
    req_seq,
    req_age_tag,
    req_metadata,
    req_handle,
    rsp_accepted,
    rsp_seq,
    rsp_age_tag,
    rsp_metadata,
    rsp_handle,
    rsp_malformed,
    rsp_stale,
    rsp_seq_mismatch,
    rsp_duplicate,
    outstanding_valid,
    outstanding_seq,
    outstanding_age,
    outstanding_timer_expired,
    transport_fault
);
    input clk;
    input rst_n;
    input enable;
    input [2:0] mode_select;
    input [7:0] freshness_limit;
    input [7:0] timeout_limit;
    input [15:0] sequence_counter;
    output req_stream_valid;
    input req_stream_ready;
    output [127:0] req_stream_data;
    input rsp_stream_valid;
    output rsp_stream_ready;
    input [127:0] rsp_stream_data;
    output req_issued;
    output [15:0] req_seq;
    output [7:0] req_age_tag;
    output [31:0] req_metadata;
    output [15:0] req_handle;
    output rsp_accepted;
    output [15:0] rsp_seq;
    output [7:0] rsp_age_tag;
    output [31:0] rsp_metadata;
    output [15:0] rsp_handle;
    output rsp_malformed;
    output rsp_stale;
    output rsp_seq_mismatch;
    output rsp_duplicate;
    output outstanding_valid;
    output [15:0] outstanding_seq;
    output [7:0] outstanding_age;
    output outstanding_timer_expired;
    output transport_fault;

    reg req_stream_valid_r;
    reg [127:0] req_stream_data_r;
    reg rsp_stream_ready_r;
    reg req_issued_r;
    reg [15:0] req_seq_r;
    reg [7:0] req_age_tag_r;
    reg [31:0] req_metadata_r;
    reg [15:0] req_handle_r;
    reg rsp_accepted_r;
    reg [15:0] rsp_seq_r;
    reg [7:0] rsp_age_tag_r;
    reg [31:0] rsp_metadata_r;
    reg [15:0] rsp_handle_r;
    reg rsp_malformed_r;
    reg rsp_stale_r;
    reg rsp_seq_mismatch_r;
    reg rsp_duplicate_r;
    reg outstanding_valid_r;
    reg [15:0] outstanding_seq_r;
    reg [7:0] outstanding_age_r;
    reg outstanding_timer_expired_r;
    reg transport_fault_r;

    reg [7:0] timer_r;
    reg [7:0] age_counter_r;
    reg [15:0] pending_seq_r;
    reg pending_seq_valid_r;
    reg rsp_seen_r;

    assign req_stream_valid = req_stream_valid_r;
    assign req_stream_data = req_stream_data_r;
    assign rsp_stream_ready = rsp_stream_ready_r;
    assign req_issued = req_issued_r;
    assign req_seq = req_seq_r;
    assign req_age_tag = req_age_tag_r;
    assign req_metadata = req_metadata_r;
    assign req_handle = req_handle_r;
    assign rsp_accepted = rsp_accepted_r;
    assign rsp_seq = rsp_seq_r;
    assign rsp_age_tag = rsp_age_tag_r;
    assign rsp_metadata = rsp_metadata_r;
    assign rsp_handle = rsp_handle_r;
    assign rsp_malformed = rsp_malformed_r;
    assign rsp_stale = rsp_stale_r;
    assign rsp_seq_mismatch = rsp_seq_mismatch_r;
    assign rsp_duplicate = rsp_duplicate_r;
    assign outstanding_valid = outstanding_valid_r;
    assign outstanding_seq = outstanding_seq_r;
    assign outstanding_age = outstanding_age_r;
    assign outstanding_timer_expired = outstanding_timer_expired_r;
    assign transport_fault = transport_fault_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            req_stream_valid_r <= 1'b0;
            req_stream_data_r <= 128'h0000_0000_0000_0000_0000_0000_0000_0000;
            rsp_stream_ready_r <= 1'b1;
            req_issued_r <= 1'b0;
            req_seq_r <= 16'h0000;
            req_age_tag_r <= 8'h00;
            req_metadata_r <= 32'h0000_0000;
            req_handle_r <= 16'h0000;
            rsp_accepted_r <= 1'b0;
            rsp_seq_r <= 16'h0000;
            rsp_age_tag_r <= 8'h00;
            rsp_metadata_r <= 32'h0000_0000;
            rsp_handle_r <= 16'h0000;
            rsp_malformed_r <= 1'b0;
            rsp_stale_r <= 1'b0;
            rsp_seq_mismatch_r <= 1'b0;
            rsp_duplicate_r <= 1'b0;
            outstanding_valid_r <= 1'b0;
            outstanding_seq_r <= 16'h0000;
            outstanding_age_r <= 8'h00;
            outstanding_timer_expired_r <= 1'b0;
            transport_fault_r <= 1'b0;
            timer_r <= 8'h00;
            age_counter_r <= 8'h00;
            pending_seq_r <= 16'h0000;
            pending_seq_valid_r <= 1'b0;
            rsp_seen_r <= 1'b0;
        end else begin
            req_issued_r <= 1'b0;
            rsp_accepted_r <= 1'b0;
            rsp_malformed_r <= 1'b0;
            rsp_stale_r <= 1'b0;
            rsp_seq_mismatch_r <= 1'b0;
            rsp_duplicate_r <= 1'b0;
            outstanding_timer_expired_r <= 1'b0;
            transport_fault_r <= 1'b0;

            if (enable && !outstanding_valid_r) begin
                req_stream_valid_r <= 1'b1;
                req_seq_r <= sequence_counter;
                req_age_tag_r <= age_counter_r;
                req_metadata_r <= {mode_select, freshness_limit, timeout_limit, 13'h0000};
                req_handle_r <= sequence_counter;
                req_stream_data_r <= {sequence_counter, age_counter_r, {mode_select, freshness_limit, timeout_limit, 13'h0000}, sequence_counter, 48'h0000_0000_0000};
                if (req_stream_ready) begin
                    req_issued_r <= 1'b1;
                    outstanding_valid_r <= 1'b1;
                    outstanding_seq_r <= sequence_counter;
                    outstanding_age_r <= age_counter_r;
                    pending_seq_r <= sequence_counter;
                    pending_seq_valid_r <= 1'b1;
                    req_stream_valid_r <= 1'b0;
                    timer_r <= 8'h00;
                end
            end else begin
                req_stream_valid_r <= 1'b0;
            end

            if (outstanding_valid_r) begin
                if (timer_r == timeout_limit) begin
                    outstanding_timer_expired_r <= 1'b1;
                    transport_fault_r <= 1'b1;
                    outstanding_valid_r <= 1'b0;
                    pending_seq_valid_r <= 1'b0;
                end else begin
                    timer_r <= timer_r + 8'h01;
                end
            end else begin
                timer_r <= 8'h00;
            end

            if (rsp_stream_valid && rsp_stream_ready_r) begin
                rsp_seen_r <= 1'b1;
                rsp_seq_r <= rsp_stream_data[15:0];
                rsp_age_tag_r <= rsp_stream_data[23:16];
                rsp_metadata_r <= rsp_stream_data[55:24];
                rsp_handle_r <= rsp_stream_data[71:56];
                if (rsp_stream_data[127:120] == 8'hA5) begin
                    if (!outstanding_valid_r) begin
                        rsp_stale_r <= 1'b1;
                        rsp_malformed_r <= 1'b0;
                    end else if (rsp_stream_data[15:0] != outstanding_seq_r) begin
                        rsp_seq_mismatch_r <= 1'b1;
                        rsp_stale_r <= 1'b1;
                    end else if (rsp_stream_data[23:16] > freshness_limit) begin
                        rsp_stale_r <= 1'b1;
                    end else if (rsp_seen_r) begin
                        rsp_duplicate_r <= 1'b1;
                    end else begin
                        rsp_accepted_r <= 1'b1;
                        outstanding_valid_r <= 1'b0;
                        pending_seq_valid_r <= 1'b0;
                        timer_r <= 8'h00;
                    end
                end else begin
                    rsp_malformed_r <= 1'b1;
                    transport_fault_r <= 1'b1;
                end
            end

            if (rsp_seen_r && !(rsp_stream_valid && rsp_stream_ready_r)) begin
                rsp_seen_r <= 1'b0;
            end

            age_counter_r <= age_counter_r + 8'h01;
        end
    end
endmodule
