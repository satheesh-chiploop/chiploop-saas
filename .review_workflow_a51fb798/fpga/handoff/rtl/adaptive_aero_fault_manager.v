module adaptive_aero_fault_manager (
    clk,
    reset_n,
    cfg_clear_fault,
    cfg_irq_enable,
    rsp_accept_pulse,
    rsp_discard_pulse,
    fault_timeout_sticky,
    fault_stale_sticky,
    fault_invalid_sticky,
    fault_queue_full_sticky,
    fault_host_not_ready_sticky,
    reg_request_pending,
    cfg_fault_status,
    cfg_mode_status,
    last_fault_code,
    irq
);
    input clk;
    input reset_n;
    input cfg_clear_fault;
    input cfg_irq_enable;
    input rsp_accept_pulse;
    input rsp_discard_pulse;
    input fault_timeout_sticky;
    input fault_stale_sticky;
    input fault_invalid_sticky;
    input fault_queue_full_sticky;
    input fault_host_not_ready_sticky;
    input reg_request_pending;
    output reg [7:0] cfg_fault_status;
    output reg [7:0] cfg_mode_status;
    output reg [7:0] last_fault_code;
    output reg irq;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            cfg_fault_status <= 8'h00;
            cfg_mode_status <= 8'h00;
            last_fault_code <= 8'h00;
            irq <= 1'b0;
        end else begin
            if (cfg_clear_fault) begin
                cfg_fault_status <= 8'h00;
                last_fault_code <= 8'h00;
                irq <= 1'b0;
            end else begin
                cfg_fault_status[0] <= reg_request_pending;
                cfg_fault_status[1] <= fault_timeout_sticky;
                cfg_fault_status[2] <= fault_stale_sticky;
                cfg_fault_status[3] <= fault_invalid_sticky;
                cfg_fault_status[4] <= fault_queue_full_sticky;
                cfg_fault_status[5] <= fault_host_not_ready_sticky;
                cfg_fault_status[7:6] <= 2'b00;
                if (fault_timeout_sticky) last_fault_code <= 8'h01;
                else if (fault_stale_sticky) last_fault_code <= 8'h02;
                else if (fault_invalid_sticky) last_fault_code <= 8'h03;
                else if (fault_queue_full_sticky) last_fault_code <= 8'h04;
                else if (fault_host_not_ready_sticky) last_fault_code <= 8'h05;
                if (cfg_irq_enable && (fault_timeout_sticky | fault_stale_sticky | fault_invalid_sticky | fault_queue_full_sticky | fault_host_not_ready_sticky | rsp_accept_pulse | rsp_discard_pulse)) irq <= 1'b1;
                else if (rsp_accept_pulse && !cfg_irq_enable) irq <= 1'b0;
            end
            cfg_mode_status <= {6'h00, reg_request_pending, cfg_irq_enable};
        end
    end
endmodule
