module adaptive_aero_control_csr_mmio (
    clk,
    reset_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_sel_i,
    wb_we_i,
    wb_stb_i,
    wb_cyc_i,
    wb_ack_o,
    wb_err_o,
    cfg_enable_o,
    cfg_arm_o,
    cfg_mode_o,
    cfg_velocity_setpoint_o,
    cfg_clamp_min_o,
    cfg_clamp_max_o,
    cfg_timeout_threshold_o,
    cfg_sequence_counter_o,
    cfg_fault_clear_w1c_o,
    irq_enable_o,
    status_fault_sticky_i,
    status_response_ready_i,
    status_fresh_i,
    status_stale_i,
    status_timeout_i,
    status_last_seen_sequence_i,
    status_actuator_cmd_i,
    status_irq_summary_i
);
input clk;
input reset_n;
input [31:0] wb_adr_i;
input [31:0] wb_dat_i;
output [31:0] wb_dat_o;
input [3:0] wb_sel_i;
input wb_we_i;
input wb_stb_i;
input wb_cyc_i;
output wb_ack_o;
output wb_err_o;
output cfg_enable_o;
output cfg_arm_o;
output [1:0] cfg_mode_o;
output [31:0] cfg_velocity_setpoint_o;
output [31:0] cfg_clamp_min_o;
output [31:0] cfg_clamp_max_o;
output [15:0] cfg_timeout_threshold_o;
output [15:0] cfg_sequence_counter_o;
output [7:0] cfg_fault_clear_w1c_o;
output [3:0] irq_enable_o;
input [7:0] status_fault_sticky_i;
input status_response_ready_i;
input status_fresh_i;
input status_stale_i;
input status_timeout_i;
input [15:0] status_last_seen_sequence_i;
input [31:0] status_actuator_cmd_i;
input [3:0] status_irq_summary_i;
reg [31:0] wb_dat_o_r;
reg wb_ack_o_r;
reg wb_err_o_r;
reg [31:0] cfg_ctrl_reg;
reg [31:0] cfg_velocity_setpoint_reg;
reg [31:0] cfg_clamp_min_reg;
reg [31:0] cfg_clamp_max_reg;
reg [15:0] cfg_timeout_threshold_reg;
reg [15:0] cfg_sequence_counter_reg;
reg [7:0] cfg_fault_clear_w1c_reg;
reg [7:0] sticky_fault_shadow;
reg [15:0] last_seen_sequence_shadow;
reg [31:0] actuator_cmd_shadow;
reg [3:0] irq_status_shadow;

wire [31:0] read_data_next;
wire [31:0] status_readback;
wire [31:0] irq_status_readback;
wire [31:0] ctrl_readback;
wire [31:0] velocity_readback;
wire [31:0] clamp_min_readback;
wire [31:0] clamp_max_readback;
wire [31:0] timeout_readback;
wire [31:0] sequence_readback;
wire [31:0] fault_clear_readback;
wire [31:0] actuator_readback;
wire [31:0] status_reg_readback;
wire [31:0] irq_reg_readback;
wire [31:0] addr_word;
wire [7:0] addr_byte;
wire bus_hit;
wire bus_write;

assign cfg_enable_o = cfg_ctrl_reg[0];
assign cfg_arm_o = cfg_ctrl_reg[1];
assign cfg_mode_o = cfg_ctrl_reg[3:2];
assign irq_enable_o = cfg_ctrl_reg[7:4];
assign cfg_velocity_setpoint_o = cfg_velocity_setpoint_reg;
assign cfg_clamp_min_o = cfg_clamp_min_reg;
assign cfg_clamp_max_o = cfg_clamp_max_reg;
assign cfg_timeout_threshold_o = cfg_timeout_threshold_reg;
assign cfg_sequence_counter_o = cfg_sequence_counter_reg;
assign cfg_fault_clear_w1c_o = cfg_fault_clear_w1c_reg;
assign status_reg_readback = {4'b0, status_last_seen_sequence_i, status_timeout_i, status_stale_i, status_fresh_i, status_response_ready_i, status_fault_sticky_i};
assign irq_reg_readback = {28'b0, status_irq_summary_i};
assign ctrl_readback = cfg_ctrl_reg;
assign velocity_readback = cfg_velocity_setpoint_reg;
assign clamp_min_readback = cfg_clamp_min_reg;
assign clamp_max_readback = cfg_clamp_max_reg;
assign timeout_readback = {16'b0, cfg_timeout_threshold_reg};
assign sequence_readback = {16'b0, cfg_sequence_counter_reg};
assign fault_clear_readback = {24'b0, cfg_fault_clear_w1c_reg};
assign actuator_readback = status_actuator_cmd_i;
assign status_fault_sticky_i_unused = 1'b0;
assign bus_hit = wb_cyc_i & wb_stb_i;
assign bus_write = bus_hit & wb_we_i;
assign addr_word = wb_adr_i[7:0];
assign addr_byte = wb_adr_i[7:0];

assign wb_dat_o = wb_dat_o_r;
assign wb_ack_o = wb_ack_o_r;
assign wb_err_o = wb_err_o_r;
assign status_readback = status_reg_readback;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        cfg_ctrl_reg <= 32'h00000000;
        cfg_velocity_setpoint_reg <= 32'h00000000;
        cfg_clamp_min_reg <= 32'h00000000;
        cfg_clamp_max_reg <= 32'h7fffffff;
        cfg_timeout_threshold_reg <= 16'h0000;
        cfg_sequence_counter_reg <= 16'h0000;
        cfg_fault_clear_w1c_reg <= 8'h00;
        sticky_fault_shadow <= 8'h00;
        last_seen_sequence_shadow <= 16'h0000;
        actuator_cmd_shadow <= 32'h00000000;
        irq_status_shadow <= 4'h0;
        wb_dat_o_r <= 32'h00000000;
        wb_ack_o_r <= 1'b0;
        wb_err_o_r <= 1'b0;
    end else begin
        wb_ack_o_r <= bus_hit;
        wb_err_o_r <= 1'b0;
        cfg_fault_clear_w1c_reg <= 8'h00;
        sticky_fault_shadow <= status_fault_sticky_i;
        last_seen_sequence_shadow <= status_last_seen_sequence_i;
        actuator_cmd_shadow <= status_actuator_cmd_i;
        irq_status_shadow <= status_irq_summary_i;
        if (bus_hit) begin
            case (addr_word)
                8'h00: begin
                    wb_dat_o_r <= ctrl_readback;
                    if (bus_write) begin
                        if (wb_sel_i[0]) cfg_ctrl_reg[7:0] <= wb_dat_i[7:0];
                        if (wb_sel_i[1]) cfg_ctrl_reg[15:8] <= wb_dat_i[15:8];
                        if (wb_sel_i[2]) cfg_ctrl_reg[23:16] <= wb_dat_i[23:16];
                        if (wb_sel_i[3]) cfg_ctrl_reg[31:24] <= wb_dat_i[31:24];
                    end
                end
                8'h04: begin
                    wb_dat_o_r <= velocity_readback;
                    if (bus_write) begin
                        if (wb_sel_i[0]) cfg_velocity_setpoint_reg[7:0] <= wb_dat_i[7:0];
                        if (wb_sel_i[1]) cfg_velocity_setpoint_reg[15:8] <= wb_dat_i[15:8];
                        if (wb_sel_i[2]) cfg_velocity_setpoint_reg[23:16] <= wb_dat_i[23:16];
                        if (wb_sel_i[3]) cfg_velocity_setpoint_reg[31:24] <= wb_dat_i[31:24];
                    end
                end
                8'h08: begin
                    wb_dat_o_r <= clamp_min_readback;
                    if (bus_write) begin
                        if (wb_sel_i[0]) cfg_clamp_min_reg[7:0] <= wb_dat_i[7:0];
                        if (wb_sel_i[1]) cfg_clamp_min_reg[15:8] <= wb_dat_i[15:8];
                        if (wb_sel_i[2]) cfg_clamp_min_reg[23:16] <= wb_dat_i[23:16];
                        if (wb_sel_i[3]) cfg_clamp_min_reg[31:24] <= wb_dat_i[31:24];
                    end
                end
                8'h0C: begin
                    wb_dat_o_r <= clamp_max_readback;
                    if (bus_write) begin
                        if (wb_sel_i[0]) cfg_clamp_max_reg[7:0] <= wb_dat_i[7:0];
                        if (wb_sel_i[1]) cfg_clamp_max_reg[15:8] <= wb_dat_i[15:8];
                        if (wb_sel_i[2]) cfg_clamp_max_reg[23:16] <= wb_dat_i[23:16];
                        if (wb_sel_i[3]) cfg_clamp_max_reg[31:24] <= wb_dat_i[31:24];
                    end
                end
                8'h10: begin
                    wb_dat_o_r <= timeout_readback;
                    if (bus_write) begin
                        if (wb_sel_i[0]) cfg_timeout_threshold_reg[7:0] <= wb_dat_i[7:0];
                        if (wb_sel_i[1]) cfg_timeout_threshold_reg[15:8] <= wb_dat_i[15:8];
                    end
                end
                8'h14: begin
                    wb_dat_o_r <= sequence_readback;
                    if (bus_write) begin
                        if (wb_sel_i[0]) cfg_sequence_counter_reg[7:0] <= wb_dat_i[7:0];
                        if (wb_sel_i[1]) cfg_sequence_counter_reg[15:8] <= wb_dat_i[15:8];
                    end
                end
                8'h18: begin
                    wb_dat_o_r <= fault_clear_readback;
                    if (bus_write) begin
                        if (wb_sel_i[0]) cfg_fault_clear_w1c_reg[7:0] <= wb_dat_i[7:0];
                    end
                end
                8'h1C: begin
                    wb_dat_o_r <= status_readback;
                end
                8'h20: begin
                    wb_dat_o_r <= actuator_readback;
                end
                8'h24: begin
                    wb_dat_o_r <= irq_reg_readback;
                end
                default: begin
                    wb_dat_o_r <= 32'h00000000;
                end
            endcase
        end else begin
            wb_dat_o_r <= wb_dat_o_r;
        end
    end
end
endmodule
