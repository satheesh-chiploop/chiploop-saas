module adaptive_aero_request_supervisor (
    clk,
    reset_n,
    cfg_global_enable,
    cfg_release_enable,
    cfg_clear_faults,
    cfg_request_launch,
    cfg_mode_sel,
    cfg_timeout_threshold,
    cfg_stale_age_threshold,
    cfg_request_payload,
    model_req_valid,
    model_req_data,
    model_req_ready,
    model_rsp_valid,
    model_rsp_data,
    model_rsp_ready,
    busy,
    response_ready,
    stale_rejected,
    timeout_fault,
    invalid_response,
    sequence_mismatch,
    accepted_response_summary,
    current_sequence_id,
    request_timestamp,
    sticky_fault_set,
    fault_event_pulse
);
    input clk;
    input reset_n;
    input cfg_global_enable;
    input cfg_release_enable;
    input cfg_clear_faults;
    input cfg_request_launch;
    input [1:0] cfg_mode_sel;
    input [15:0] cfg_timeout_threshold;
    input [15:0] cfg_stale_age_threshold;
    input [31:0] cfg_request_payload;
    output model_req_valid;
    output [63:0] model_req_data;
    input model_req_ready;
    input model_rsp_valid;
    input [63:0] model_rsp_data;
    output model_rsp_ready;
    output busy;
    output response_ready;
    output stale_rejected;
    output timeout_fault;
    output invalid_response;
    output sequence_mismatch;
    output [63:0] accepted_response_summary;
    output [15:0] current_sequence_id;
    output [15:0] request_timestamp;
    output [15:0] sticky_fault_set;
    output fault_event_pulse;

    reg model_req_valid_r;
    reg [63:0] model_req_data_r;
    reg model_rsp_ready_r;
    reg busy_r;
    reg response_ready_r;
    reg stale_rejected_r;
    reg timeout_fault_r;
    reg invalid_response_r;
    reg sequence_mismatch_r;
    reg [63:0] accepted_response_summary_r;
    reg [15:0] current_sequence_id_r;
    reg [15:0] request_timestamp_r;
    reg [15:0] sticky_fault_set_r;
    reg fault_event_pulse_r;
    reg [15:0] timeout_cnt;
    reg [15:0] age_cnt;
    reg outstanding;
    reg [15:0] seq_next;
    reg [63:0] req_word;
    reg [63:0] rsp_word;
    reg rsp_accept;

    assign model_req_valid = model_req_valid_r;
    assign model_req_data = model_req_data_r;
    assign model_rsp_ready = model_rsp_ready_r;
    assign busy = busy_r;
    assign response_ready = response_ready_r;
    assign stale_rejected = stale_rejected_r;
    assign timeout_fault = timeout_fault_r;
    assign invalid_response = invalid_response_r;
    assign sequence_mismatch = sequence_mismatch_r;
    assign accepted_response_summary = accepted_response_summary_r;
    assign current_sequence_id = current_sequence_id_r;
    assign request_timestamp = request_timestamp_r;
    assign sticky_fault_set = sticky_fault_set_r;
    assign fault_event_pulse = fault_event_pulse_r;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            model_req_valid_r <= 1'b0;
            model_req_data_r <= 64'h0000000000000000;
            model_rsp_ready_r <= 1'b1;
            busy_r <= 1'b0;
            response_ready_r <= 1'b0;
            stale_rejected_r <= 1'b0;
            timeout_fault_r <= 1'b0;
            invalid_response_r <= 1'b0;
            sequence_mismatch_r <= 1'b0;
            accepted_response_summary_r <= 64'h0000000000000000;
            current_sequence_id_r <= 16'h0000;
            request_timestamp_r <= 16'h0000;
            sticky_fault_set_r <= 16'h0001;
            fault_event_pulse_r <= 1'b0;
            timeout_cnt <= 16'h0000;
            age_cnt <= 16'h0000;
            outstanding <= 1'b0;
            seq_next <= 16'h0001;
            req_word <= 64'h0000000000000000;
            rsp_word <= 64'h0000000000000000;
            rsp_accept <= 1'b0;
        end else begin
            fault_event_pulse_r <= 1'b0;
            rsp_accept <= 1'b0;
            if (cfg_clear_faults) sticky_fault_set_r <= 16'h0000;
            if (cfg_request_launch && cfg_global_enable && cfg_release_enable && !outstanding && (sticky_fault_set_r == 16'h0000)) begin
                outstanding <= 1'b1;
                busy_r <= 1'b1;
                response_ready_r <= 1'b0;
                current_sequence_id_r <= seq_next;
                request_timestamp_r <= request_timestamp_r + 16'h0001;
                timeout_cnt <= 16'h0000;
                age_cnt <= 16'h0000;
                req_word <= {cfg_mode_sel, seq_next, cfg_request_payload, 8'hA5, 8'h5A, 6'b0};
                model_req_data_r <= {cfg_mode_sel, seq_next, cfg_request_payload, 8'hA5, 8'h5A, 6'b0};
                model_req_valid_r <= 1'b1;
                seq_next <= seq_next + 16'h0001;
            end
            if (outstanding) begin
                if (model_req_valid_r && model_req_ready) model_req_valid_r <= 1'b0;
                if (timeout_cnt != cfg_timeout_threshold) timeout_cnt <= timeout_cnt + 16'h0001;
                if (age_cnt != cfg_stale_age_threshold) age_cnt <= age_cnt + 16'h0001;
                if (cfg_timeout_threshold != 16'h0000 && timeout_cnt >= cfg_timeout_threshold) begin
                    timeout_fault_r <= 1'b1;
                    sticky_fault_set_r <= sticky_fault_set_r | 16'h0002;
                    fault_event_pulse_r <= 1'b1;
                    outstanding <= 1'b0;
                    busy_r <= 1'b0;
                    model_req_valid_r <= 1'b0;
                end
                if (model_rsp_valid) begin
                    rsp_word <= model_rsp_data;
                    if (model_rsp_data[63:48] != current_sequence_id_r) begin
                        sequence_mismatch_r <= 1'b1;
                        sticky_fault_set_r <= sticky_fault_set_r | 16'h0008;
                        fault_event_pulse_r <= 1'b1;
                    end else if ((cfg_stale_age_threshold != 16'h0000) && (age_cnt >= cfg_stale_age_threshold)) begin
                        stale_rejected_r <= 1'b1;
                        sticky_fault_set_r <= sticky_fault_set_r | 16'h0004;
                        fault_event_pulse_r <= 1'b1;
                    end else if ((model_rsp_data[47:32] == 16'h0000) || (model_rsp_data[47:32] == 16'hFFFF)) begin
                        invalid_response_r <= 1'b1;
                        sticky_fault_set_r <= sticky_fault_set_r | 16'h0010;
                        fault_event_pulse_r <= 1'b1;
                    end else begin
                        response_ready_r <= 1'b1;
                        accepted_response_summary_r <= model_rsp_data;
                        rsp_accept <= 1'b1;
                    end
                    outstanding <= 1'b0;
                    busy_r <= 1'b0;
                    model_req_valid_r <= 1'b0;
                end
            end
            if (cfg_clear_faults) begin
                stale_rejected_r <= 1'b0;
                timeout_fault_r <= 1'b0;
                invalid_response_r <= 1'b0;
                sequence_mismatch_r <= 1'b0;
                response_ready_r <= 1'b0;
            end
            if (!cfg_global_enable || !cfg_release_enable) begin
                model_rsp_ready_r <= 1'b1;
            end else begin
                model_rsp_ready_r <= outstanding;
            end
        end
    end
endmodule
