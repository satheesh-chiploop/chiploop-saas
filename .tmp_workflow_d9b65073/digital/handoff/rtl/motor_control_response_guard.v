module motor_control_response_guard (
    input         clk,
    input         reset_n,
    input         request_accepted,
    input  [127:0] request_payload,
    input         service_rsp_valid,
    output        service_rsp_ready,
    input  [127:0] service_rsp_payload,
    input         busy_i,
    input  [15:0] cfg_sequence_num,
    input  [15:0] cfg_timeout_budget,
    input  [15:0] cfg_freshness_limit,
    input  [15:0] cfg_cmd_min,
    input  [15:0] cfg_cmd_max,
    input  [31:0] cfg_safe_fallback_cfg,
    input         host_clear_faults,
    input         host_emergency_stop,
    input         host_done_mode_latch,
    output reg [31:0] actuator_cmd_o,
    output reg    actuator_cmd_valid,
    input         actuator_cmd_ready,
    output reg    busy_o,
    output reg    done_o,
    output reg [31:0] status_o
);

reg [15:0] active_seq;
reg [7:0] age_cnt;
reg sticky_fault;
reg sticky_stale_reject;
reg sticky_timeout_fault;
reg sticky_seq_mismatch;
reg sticky_clamp_active;
reg sticky_fallback_active;
reg init_complete;
reg last_rsp_ok;

assign service_rsp_ready = busy_i;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        active_seq <= 16'h0000;
        age_cnt <= 8'h00;
        sticky_fault <= 1'b0;
        sticky_stale_reject <= 1'b0;
        sticky_timeout_fault <= 1'b0;
        sticky_seq_mismatch <= 1'b0;
        sticky_clamp_active <= 1'b0;
        sticky_fallback_active <= 1'b1;
        init_complete <= 1'b0;
        last_rsp_ok <= 1'b0;
        actuator_cmd_o <= 32'h00000000;
        actuator_cmd_valid <= 1'b0;
        busy_o <= 1'b0;
        done_o <= 1'b0;
        status_o <= 32'h00000000;
    end else begin
        done_o <= 1'b0;
        if (host_clear_faults) begin
            sticky_fault <= 1'b0;
            sticky_stale_reject <= 1'b0;
            sticky_timeout_fault <= 1'b0;
            sticky_seq_mismatch <= 1'b0;
            sticky_clamp_active <= 1'b0;
            sticky_fallback_active <= 1'b0;
        end
        if (host_emergency_stop) begin
            sticky_fault <= 1'b1;
            sticky_fallback_active <= 1'b1;
            actuator_cmd_o <= cfg_safe_fallback_cfg;
            actuator_cmd_valid <= 1'b1;
            last_rsp_ok <= 1'b0;
        end
        if (request_accepted) begin
            busy_o <= 1'b1;
            active_seq <= cfg_sequence_num;
            age_cnt <= 8'h00;
        end else if (busy_i) begin
            age_cnt <= age_cnt + 8'h01;
        end
        if (busy_i && service_rsp_valid) begin
            if (service_rsp_payload[15:0] != active_seq) begin
                sticky_fault <= 1'b1;
                sticky_seq_mismatch <= 1'b1;
                sticky_fallback_active <= 1'b1;
                actuator_cmd_o <= cfg_safe_fallback_cfg;
                actuator_cmd_valid <= 1'b1;
                busy_o <= 1'b0;
                done_o <= 1'b1;
                last_rsp_ok <= 1'b0;
            end else if (cfg_timeout_budget != 16'h0000 && age_cnt >= cfg_timeout_budget[7:0]) begin
                sticky_fault <= 1'b1;
                sticky_timeout_fault <= 1'b1;
                sticky_fallback_active <= 1'b1;
                actuator_cmd_o <= cfg_safe_fallback_cfg;
                actuator_cmd_valid <= 1'b1;
                busy_o <= 1'b0;
                done_o <= 1'b1;
                last_rsp_ok <= 1'b0;
            end else begin
                actuator_cmd_o <= service_rsp_payload[31:0];
                if (service_rsp_payload[31:16] < cfg_cmd_min) begin
                    actuator_cmd_o <= {16'h0000, cfg_cmd_min};
                    sticky_clamp_active <= 1'b1;
                end else if (service_rsp_payload[31:16] > cfg_cmd_max) begin
                    actuator_cmd_o <= {16'h0000, cfg_cmd_max};
                    sticky_clamp_active <= 1'b1;
                end
                actuator_cmd_valid <= 1'b1;
                busy_o <= 1'b0;
                done_o <= 1'b1;
                init_complete <= 1'b1;
                last_rsp_ok <= 1'b1;
                sticky_fallback_active <= 1'b0;
            end
        end
        if (actuator_cmd_valid && actuator_cmd_ready) begin
            actuator_cmd_valid <= 1'b0;
        end
        if (busy_i && cfg_freshness_limit != 16'h0000 && age_cnt > cfg_freshness_limit[7:0]) begin
            sticky_fault <= 1'b1;
            sticky_stale_reject <= 1'b1;
            sticky_fallback_active <= 1'b1;
            actuator_cmd_o <= cfg_safe_fallback_cfg;
            actuator_cmd_valid <= 1'b1;
            busy_o <= 1'b0;
            done_o <= 1'b1;
            last_rsp_ok <= 1'b0;
        end
        status_o <= {22'h000000, last_rsp_ok, init_complete, busy_o, done_o, sticky_fallback_active, sticky_clamp_active, sticky_seq_mismatch, sticky_timeout_fault, sticky_stale_reject, sticky_fault};
    end
end

endmodule
