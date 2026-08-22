module adaptive_aero_safety_control (
    clk,
    reset_n,
    cfg_enable,
    cfg_fault_clear,
    cfg_timeout_cycles,
    cfg_act_min,
    cfg_act_max,
    cfg_act_safe,
    cfg_output_mode,
    pending,
    busy,
    seq_last_accepted,
    req_seq,
    rsp_seq,
    rsp_cmd,
    fault_transport,
    fault_malformed,
    fault_stale,
    fault_timeout,
    fault_clamp,
    fault_sticky,
    timeout_active,
    fallback_active,
    act_cmd_valid,
    act_cmd,
    status_busy,
    status_pending,
    status_seq_last_accepted,
    status_req_seq,
    status_rsp_seq,
    status_rsp_cmd
);
    input clk;
    input reset_n;
    input cfg_enable;
    input cfg_fault_clear;
    input [31:0] cfg_timeout_cycles;
    input [15:0] cfg_act_min;
    input [15:0] cfg_act_max;
    input [15:0] cfg_act_safe;
    input [1:0] cfg_output_mode;
    input pending;
    input busy;
    input [15:0] seq_last_accepted;
    input [15:0] req_seq;
    input [15:0] rsp_seq;
    input [15:0] rsp_cmd;
    input fault_transport;
    input fault_malformed;
    input fault_stale;
    output reg fault_timeout;
    output reg fault_clamp;
    output reg [31:0] fault_sticky;
    output reg timeout_active;
    output reg fallback_active;
    output reg act_cmd_valid;
    output reg [15:0] act_cmd;
    output reg status_busy;
    output reg status_pending;
    output reg [15:0] status_seq_last_accepted;
    output reg [15:0] status_req_seq;
    output reg [15:0] status_rsp_seq;
    output reg [15:0] status_rsp_cmd;
    reg [31:0] timeout_count;
    reg timeout_running;
    reg [15:0] accepted_cmd;
    reg [31:0] fault_sticky_next;
    reg fault_timeout_next;
    reg fault_clamp_next;
    reg timeout_active_next;
    reg fallback_active_next;
    reg act_cmd_valid_next;
    reg [15:0] act_cmd_next;
    reg [31:0] timeout_count_next;
    reg timeout_running_next;
    reg [15:0] accepted_cmd_next;
    reg status_busy_next;
    reg status_pending_next;
    reg [15:0] status_seq_last_accepted_next;
    reg [15:0] status_req_seq_next;
    reg [15:0] status_rsp_seq_next;
    reg [15:0] status_rsp_cmd_next;
    reg sticky_clear_ok;
    reg [15:0] limited_cmd;
    reg clamp_hit;
    reg timeout_hit;

    always @(*) begin
        fault_sticky_next = fault_sticky;
        fault_timeout_next = 1'b0;
        fault_clamp_next = 1'b0;
        timeout_active_next = 1'b0;
        fallback_active_next = 1'b1;
        act_cmd_valid_next = 1'b0;
        act_cmd_next = act_cmd;
        timeout_count_next = timeout_count;
        timeout_running_next = timeout_running;
        accepted_cmd_next = accepted_cmd;
        status_busy_next = busy;
        status_pending_next = pending;
        status_seq_last_accepted_next = seq_last_accepted;
        status_req_seq_next = req_seq;
        status_rsp_seq_next = rsp_seq;
        status_rsp_cmd_next = rsp_cmd;
        sticky_clear_ok = (~cfg_enable) | (~pending);
        clamp_hit = 1'b0;
        limited_cmd = rsp_cmd;
        timeout_hit = 1'b0;

        if (cfg_act_max < cfg_act_min) begin
            if (rsp_cmd < cfg_act_min) begin
                limited_cmd = cfg_act_min;
                clamp_hit = 1'b1;
            end else begin
                limited_cmd = cfg_act_min;
                clamp_hit = 1'b1;
            end
        end else begin
            if (rsp_cmd < cfg_act_min) begin
                limited_cmd = cfg_act_min;
                clamp_hit = 1'b1;
            end else if (rsp_cmd > cfg_act_max) begin
                limited_cmd = cfg_act_max;
                clamp_hit = 1'b1;
            end else begin
                limited_cmd = rsp_cmd;
            end
        end

        if (fault_transport | fault_malformed | fault_stale) begin
            fault_sticky_next[0] = fault_sticky_next[0] | fault_transport;
            fault_sticky_next[1] = fault_sticky_next[1] | fault_malformed;
            fault_sticky_next[2] = fault_sticky_next[2] | fault_stale;
        end

        if (pending && timeout_running && (timeout_count != 32'h00000000)) begin
            timeout_count_next = timeout_count - 32'h00000001;
            timeout_active_next = 1'b1;
            if (timeout_count == 32'h00000001) begin
                timeout_hit = 1'b1;
            end
        end else if (pending && (~timeout_running)) begin
            if (cfg_timeout_cycles != 32'h00000000) begin
                timeout_count_next = cfg_timeout_cycles;
                timeout_running_next = 1'b1;
                timeout_active_next = 1'b1;
            end
        end

        if (timeout_hit) begin
            fault_timeout_next = 1'b1;
            fault_sticky_next[3] = 1'b1;
            timeout_active_next = 1'b1;
            timeout_running_next = 1'b0;
        end

        if (clamp_hit) begin
            fault_clamp_next = 1'b1;
            fault_sticky_next[4] = 1'b1;
        end

        if (cfg_fault_clear && sticky_clear_ok) begin
            fault_sticky_next = 32'h00000000;
        end

        if (cfg_enable && pending && (~fault_transport) && (~fault_malformed) && (~fault_stale) && (~timeout_hit)) begin
            act_cmd_next = limited_cmd;
            act_cmd_valid_next = 1'b1;
            accepted_cmd_next = limited_cmd;
            fallback_active_next = 1'b0;
        end else begin
            act_cmd_next = cfg_act_safe;
            act_cmd_valid_next = 1'b0;
            fallback_active_next = 1'b1;
        end

        if ((~cfg_enable) || fault_transport || fault_malformed || fault_stale || timeout_hit || (|fault_sticky_next[4:0])) begin
            act_cmd_valid_next = 1'b0;
            fallback_active_next = 1'b1;
        end

        if ((~cfg_enable) && cfg_fault_clear) begin
            fault_sticky_next = 32'h00000000;
        end

        if ((~pending) && cfg_enable) begin
            timeout_running_next = 1'b0;
            timeout_count_next = 32'h00000000;
            timeout_active_next = 1'b0;
        end
    end

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            fault_timeout <= 1'b0;
            fault_clamp <= 1'b0;
            fault_sticky <= 32'h00000000;
            timeout_active <= 1'b0;
            fallback_active <= 1'b1;
            act_cmd_valid <= 1'b0;
            act_cmd <= 16'h0000;
            status_busy <= 1'b0;
            status_pending <= 1'b0;
            status_seq_last_accepted <= 16'h0000;
            status_req_seq <= 16'h0000;
            status_rsp_seq <= 16'h0000;
            status_rsp_cmd <= 16'h0000;
            timeout_count <= 32'h00000000;
            timeout_running <= 1'b0;
            accepted_cmd <= 16'h0000;
        end else begin
            fault_timeout <= fault_timeout_next;
            fault_clamp <= fault_clamp_next;
            fault_sticky <= fault_sticky_next;
            timeout_active <= timeout_active_next;
            fallback_active <= fallback_active_next;
            act_cmd_valid <= act_cmd_valid_next;
            act_cmd <= act_cmd_next;
            status_busy <= busy;
            status_pending <= pending;
            status_seq_last_accepted <= seq_last_accepted;
            status_req_seq <= req_seq;
            status_rsp_seq <= rsp_seq;
            status_rsp_cmd <= rsp_cmd;
            timeout_count <= timeout_count_next;
            timeout_running <= timeout_running_next;
            accepted_cmd <= accepted_cmd_next;
        end
    end
endmodule
