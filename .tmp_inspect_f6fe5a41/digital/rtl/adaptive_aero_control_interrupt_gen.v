module adaptive_aero_control_interrupt_gen (
    clk,
    reset_n,
    irq_enable_i,
    response_ready_pulse_i,
    stale_i,
    timeout_i,
    fault_sticky_i,
    irq_o,
    irq_status_o
);
input clk;
input reset_n;
input [3:0] irq_enable_i;
input response_ready_pulse_i;
input stale_i;
input timeout_i;
input [7:0] fault_sticky_i;
output irq_o;
output [3:0] irq_status_o;
reg irq_o_r;
reg [3:0] irq_status_r;
reg response_ready_d;
reg stale_d;
reg timeout_d;
reg fault_d;

assign irq_o = irq_o_r;
assign irq_status_o = irq_status_r;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        irq_o_r <= 1'b0;
        irq_status_r <= 4'h0;
        response_ready_d <= 1'b0;
        stale_d <= 1'b0;
        timeout_d <= 1'b0;
        fault_d <= 1'b0;
    end else begin
        irq_status_r[0] <= response_ready_pulse_i;
        irq_status_r[1] <= stale_i;
        irq_status_r[2] <= timeout_i;
        irq_status_r[3] <= (fault_sticky_i != 8'h00);
        irq_o_r <= ((response_ready_pulse_i & irq_enable_i[0]) |
                    (stale_i & irq_enable_i[1]) |
                    (timeout_i & irq_enable_i[2]) |
                    ((fault_sticky_i != 8'h00) & irq_enable_i[3]));
        response_ready_d <= response_ready_pulse_i;
        stale_d <= stale_i;
        timeout_d <= timeout_i;
        fault_d <= (fault_sticky_i != 8'h00);
    end
end
endmodule
