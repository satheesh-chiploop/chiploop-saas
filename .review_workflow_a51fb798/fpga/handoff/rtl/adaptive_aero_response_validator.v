module adaptive_aero_response_validator (
    clk,
    reset_n,
    host_resp_stream_valid,
    host_resp_stream_data,
    host_resp_stream_ready,
    cfg_timeout_cycles,
    cfg_response_seq,
    req_launch_pulse,
    rsp_packet_128,
    rsp_accept_pulse,
    rsp_valid_result,
    rsp_discard_pulse,
    rsp_match_seq,
    last_accepted_response_id,
    discarded_response_count,
    timeout_event_count,
    stale_event_count,
    fault_timeout_sticky,
    fault_stale_sticky,
    fault_invalid_sticky
);
    input clk;
    input reset_n;
    input host_resp_stream_valid;
    input [127:0] host_resp_stream_data;
    output reg host_resp_stream_ready;
    input [23:0] cfg_timeout_cycles;
    input [15:0] cfg_response_seq;
    input req_launch_pulse;
    output reg [127:0] rsp_packet_128;
    output reg rsp_accept_pulse;
    output reg rsp_valid_result;
    output reg rsp_discard_pulse;
    output reg [15:0] rsp_match_seq;
    output reg [15:0] last_accepted_response_id;
    output reg [15:0] discarded_response_count;
    output reg [15:0] timeout_event_count;
    output reg [15:0] stale_event_count;
    output reg fault_timeout_sticky;
    output reg fault_stale_sticky;
    output reg fault_invalid_sticky;

    reg [23:0] age_count;
    reg pending;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            host_resp_stream_ready <= 1'b1;
            rsp_packet_128 <= 128'h0;
            rsp_accept_pulse <= 1'b0;
            rsp_valid_result <= 1'b0;
            rsp_discard_pulse <= 1'b0;
            rsp_match_seq <= 16'h0000;
            last_accepted_response_id <= 16'h0000;
            discarded_response_count <= 16'h0000;
            timeout_event_count <= 16'h0000;
            stale_event_count <= 16'h0000;
            fault_timeout_sticky <= 1'b0;
            fault_stale_sticky <= 1'b0;
            fault_invalid_sticky <= 1'b0;
            age_count <= 24'h000000;
            pending <= 1'b0;
        end else begin
            rsp_accept_pulse <= 1'b0;
            rsp_valid_result <= 1'b0;
            rsp_discard_pulse <= 1'b0;
            if (req_launch_pulse) begin
                pending <= 1'b1;
                age_count <= 24'h000000;
            end else if (pending) begin
                if (age_count != cfg_timeout_cycles) begin
                    age_count <= age_count + 24'h000001;
                end else begin
                    fault_timeout_sticky <= 1'b1;
                    timeout_event_count <= timeout_event_count + 16'h0001;
                    rsp_discard_pulse <= 1'b1;
                    discarded_response_count <= discarded_response_count + 16'h0001;
                    pending <= 1'b0;
                end
            end
            if (host_resp_stream_valid) begin
                rsp_packet_128 <= host_resp_stream_data;
                rsp_match_seq <= cfg_response_seq;
                if (pending && host_resp_stream_data[15:0] == cfg_response_seq) begin
                    rsp_accept_pulse <= 1'b1;
                    rsp_valid_result <= 1'b1;
                    last_accepted_response_id <= cfg_response_seq;
                    pending <= 1'b0;
                end else begin
                    rsp_discard_pulse <= 1'b1;
                    discarded_response_count <= discarded_response_count + 16'h0001;
                    fault_invalid_sticky <= 1'b1;
                    if (!pending) begin
                        fault_stale_sticky <= 1'b1;
                        stale_event_count <= stale_event_count + 16'h0001;
                    end
                end
            end
            if (!pending) begin
                age_count <= 24'h000000;
            end
        end
    end
endmodule
