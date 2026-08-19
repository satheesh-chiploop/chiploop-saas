module adaptive_aero_control_mmio (
    clk,
    rst_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_sel_i,
    wb_cyc_i,
    wb_stb_i,
    wb_we_i,
    wb_ack_o,
    wb_err_o,
    reg_control_enable,
    reg_control_clear_faults,
    reg_control_arm_safe_fallback,
    reg_control_bypass_output_hold,
    reg_control_mode,
    reg_seq_in,
    reg_age_limit,
    reg_velocity_mps,
    reg_act_min,
    reg_act_max,
    reg_act_cmd,
    reg_irq_ack,
    status_busy,
    status_command_accepted,
    status_stale_rejected,
    status_timeout_fault,
    status_invalid_input,
    status_clamp_applied,
    status_safe_fallback_active,
    status_irq_pending,
    reg_last_good,
    reg_timeout_cnt,
    reg_fault_cause
);

input clk;
input rst_n;
input [31:0] wb_adr_i;
input [31:0] wb_dat_i;
output [31:0] wb_dat_o;
input [3:0] wb_sel_i;
input wb_cyc_i;
input wb_stb_i;
input wb_we_i;
output reg wb_ack_o;
output reg wb_err_o;

output reg reg_control_enable;
output reg reg_control_clear_faults;
output reg reg_control_arm_safe_fallback;
output reg reg_control_bypass_output_hold;
output reg [3:0] reg_control_mode;
output reg [31:0] reg_seq_in;
output reg [31:0] reg_age_limit;
output reg [31:0] reg_velocity_mps;
output reg [31:0] reg_act_min;
output reg [31:0] reg_act_max;
output reg [31:0] reg_act_cmd;
output reg reg_irq_ack;

input status_busy;
input status_command_accepted;
input status_stale_rejected;
input status_timeout_fault;
input status_invalid_input;
input status_clamp_applied;
input status_safe_fallback_active;
input status_irq_pending;
input [31:0] reg_last_good;
input [31:0] reg_timeout_cnt;
input [31:0] reg_fault_cause;
reg [31:0] wb_dat_o_r;
assign wb_dat_o = wb_dat_o_r;

wire wb_xfer;
wire wb_write;
wire wb_read;
wire [7:0] wb_addr;
assign wb_xfer = wb_cyc_i & wb_stb_i;
assign wb_write = wb_xfer & wb_we_i;
assign wb_read = wb_xfer & (~wb_we_i);
assign wb_addr = wb_adr_i[7:0];

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        reg_control_enable <= 1'b0;
        reg_control_clear_faults <= 1'b0;
        reg_control_arm_safe_fallback <= 1'b0;
        reg_control_bypass_output_hold <= 1'b0;
        reg_control_mode <= 4'h0;
        reg_seq_in <= 32'h00000000;
        reg_age_limit <= 32'h00000000;
        reg_velocity_mps <= 32'h00000000;
        reg_act_min <= 32'h00000000;
        reg_act_max <= 32'hffffffff;
        reg_act_cmd <= 32'h00000000;
        reg_irq_ack <= 1'b0;
        wb_ack_o <= 1'b0;
        wb_err_o <= 1'b0;
        wb_dat_o_r <= 32'h00000000;
    end else begin
        reg_control_clear_faults <= 1'b0;
        reg_irq_ack <= 1'b0;
        wb_ack_o <= 1'b0;
        wb_err_o <= 1'b0;
        wb_dat_o_r <= 32'h00000000;

        if (wb_xfer) begin
            case (wb_addr)
                8'h00: begin
                    wb_ack_o <= 1'b1;
                    if (wb_write) begin
                        if (wb_sel_i[0]) begin
                            reg_control_enable <= wb_dat_i[0];
                            reg_control_clear_faults <= wb_dat_i[1];
                            reg_control_arm_safe_fallback <= wb_dat_i[2];
                            reg_control_bypass_output_hold <= wb_dat_i[3];
                            reg_control_mode <= wb_dat_i[7:4];
                        end
                    end else begin
                        wb_dat_o_r <= {24'h000000, reg_control_mode, reg_control_bypass_output_hold, reg_control_arm_safe_fallback, reg_control_clear_faults, reg_control_enable};
                    end
                end
                8'h04: begin
                    wb_ack_o <= 1'b1;
                    wb_dat_o_r <= {24'h000000, status_irq_pending, status_safe_fallback_active, status_clamp_applied, status_invalid_input, status_timeout_fault, status_stale_rejected, status_command_accepted, status_busy};
                end
                8'h08: begin
                    wb_ack_o <= 1'b1;
                    if (wb_write) begin
                        reg_seq_in <= wb_dat_i;
                    end else begin
                        wb_dat_o_r <= reg_seq_in;
                    end
                end
                8'h0C: begin
                    wb_ack_o <= 1'b1;
                    if (wb_write) begin
                        reg_age_limit <= wb_dat_i;
                    end else begin
                        wb_dat_o_r <= reg_age_limit;
                    end
                end
                8'h10: begin
                    wb_ack_o <= 1'b1;
                    if (wb_write) begin
                        reg_velocity_mps <= wb_dat_i;
                    end else begin
                        wb_dat_o_r <= reg_velocity_mps;
                    end
                end
                8'h14: begin
                    wb_ack_o <= 1'b1;
                    if (wb_write) begin
                        reg_act_min <= wb_dat_i;
                    end else begin
                        wb_dat_o_r <= reg_act_min;
                    end
                end
                8'h18: begin
                    wb_ack_o <= 1'b1;
                    if (wb_write) begin
                        reg_act_max <= wb_dat_i;
                    end else begin
                        wb_dat_o_r <= reg_act_max;
                    end
                end
                8'h1C: begin
                    wb_ack_o <= 1'b1;
                    if (wb_write) begin
                        reg_act_cmd <= wb_dat_i;
                    end else begin
                        wb_dat_o_r <= reg_act_cmd;
                    end
                end
                8'h20: begin
                    wb_ack_o <= 1'b1;
                    wb_dat_o_r <= reg_last_good;
                end
                8'h24: begin
                    wb_ack_o <= 1'b1;
                    wb_dat_o_r <= reg_timeout_cnt;
                end
                8'h28: begin
                    wb_ack_o <= 1'b1;
                    wb_dat_o_r <= reg_fault_cause;
                end
                8'h2C: begin
                    wb_ack_o <= 1'b1;
                    if (wb_write) begin
                        if (wb_sel_i[0] && wb_dat_i[0]) begin
                            reg_irq_ack <= 1'b1;
                        end
                    end
                end
                default: begin
                    wb_ack_o <= 1'b1;
                    wb_err_o <= 1'b1;
                    wb_dat_o_r <= 32'h00000000;
                end
            endcase
        end
    end
end

endmodule
