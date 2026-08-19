module adaptive_aero_control_csr_mmio (
    clk,
    rst_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_cyc_i,
    wb_stb_i,
    wb_we_i,
    wb_sel_i,
    wb_ack_o,
    wb_err_o,
    ctrl_enable,
    ctrl_clear_fault,
    ctrl_arm_output,
    ctrl_request_start,
    ctrl_bypass_model,
    status_busy,
    status_req_pending,
    status_rsp_seen,
    status_stale_fault,
    status_timeout_fault,
    status_range_fault,
    status_fallback_active,
    status_last_good_valid,
    timeout_cfg_cycles,
    stale_cfg_cycles,
    cmd_min,
    cmd_max,
    cmd_safe,
    seq_tx,
    seq_rx,
    meta_velocity_bucket,
    meta_mode,
    meta_env_flags,
    meta_session_id
);

input clk;
input rst_n;
input [31:0] wb_adr_i;
input [31:0] wb_dat_i;
output [31:0] wb_dat_o;
input wb_cyc_i;
input wb_stb_i;
input wb_we_i;
input [3:0] wb_sel_i;
output wb_ack_o;
output wb_err_o;
output ctrl_enable;
output ctrl_clear_fault;
output ctrl_arm_output;
output ctrl_request_start;
output ctrl_bypass_model;
input status_busy;
input status_req_pending;
input status_rsp_seen;
input status_stale_fault;
input status_timeout_fault;
input status_range_fault;
input status_fallback_active;
input status_last_good_valid;
output [31:0] timeout_cfg_cycles;
output [31:0] stale_cfg_cycles;
output [15:0] cmd_min;
output [15:0] cmd_max;
output [15:0] cmd_safe;
output [15:0] seq_tx;
input [15:0] seq_rx;
output [7:0] meta_velocity_bucket;
output [3:0] meta_mode;
output [3:0] meta_env_flags;
output [15:0] meta_session_id;
reg [31:0] wb_dat_o_r;
reg wb_ack_o_r;
reg wb_err_o_r;

reg ctrl_enable_r;
reg ctrl_clear_fault_r;
reg ctrl_arm_output_r;
reg ctrl_request_start_r;
reg ctrl_bypass_model_r;

reg [31:0] timeout_cfg_cycles_r;
reg [31:0] stale_cfg_cycles_r;
reg [15:0] cmd_min_r;
reg [15:0] cmd_max_r;
reg [15:0] cmd_safe_r;
reg [15:0] seq_tx_r;
reg [7:0] meta_velocity_bucket_r;
reg [3:0] meta_mode_r;
reg [3:0] meta_env_flags_r;
reg [15:0] meta_session_id_r;
wire wb_access;
wire wb_write;
wire wb_read;
wire [7:0] wb_addr;
reg [31:0] read_data_next;
reg wb_err_next;

assign wb_access = wb_cyc_i & wb_stb_i;
assign wb_write = wb_access & wb_we_i;
assign wb_read = wb_access & ~wb_we_i;
assign wb_addr = wb_adr_i[7:0];

assign wb_dat_o = wb_dat_o_r;
assign wb_ack_o = wb_ack_o_r;
assign wb_err_o = wb_err_o_r;

assign ctrl_enable = ctrl_enable_r;
assign ctrl_clear_fault = ctrl_clear_fault_r;
assign ctrl_arm_output = ctrl_arm_output_r;
assign ctrl_request_start = ctrl_request_start_r;
assign ctrl_bypass_model = ctrl_bypass_model_r;
assign timeout_cfg_cycles = timeout_cfg_cycles_r;
assign stale_cfg_cycles = stale_cfg_cycles_r;
assign cmd_min = cmd_min_r;
assign cmd_max = cmd_max_r;
assign cmd_safe = cmd_safe_r;
assign seq_tx = seq_tx_r;
assign meta_velocity_bucket = meta_velocity_bucket_r;
assign meta_mode = meta_mode_r;
assign meta_env_flags = meta_env_flags_r;
assign meta_session_id = meta_session_id_r;

always @(*) begin
    read_data_next = 32'h00000000;
    wb_err_next = 1'b0;
    case (wb_addr)
        8'h00: read_data_next = {27'h0000000, ctrl_bypass_model_r, ctrl_request_start_r, ctrl_arm_output_r, ctrl_clear_fault_r, ctrl_enable_r};
        8'h04: read_data_next = {24'h000000, status_last_good_valid, status_fallback_active, status_range_fault, status_timeout_fault, status_stale_fault, status_rsp_seen, status_req_pending, status_busy};
        8'h08: read_data_next = timeout_cfg_cycles_r;
        8'h0C: read_data_next = stale_cfg_cycles_r;
        8'h10: read_data_next = {16'h0000, cmd_min_r};
        8'h14: read_data_next = {16'h0000, cmd_max_r};
        8'h18: read_data_next = {16'h0000, cmd_safe_r};
        8'h1C: read_data_next = {16'h0000, seq_tx_r};
        8'h20: read_data_next = {16'h0000, seq_rx};
        8'h24: read_data_next = {meta_session_id_r, meta_env_flags_r, meta_mode_r, meta_velocity_bucket_r};
        default: begin
            read_data_next = 32'h00000000;
            if (wb_read) wb_err_next = 1'b1;
        end
    endcase
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        ctrl_enable_r <= 1'b0;
        ctrl_clear_fault_r <= 1'b0;
        ctrl_arm_output_r <= 1'b0;
        ctrl_request_start_r <= 1'b0;
        ctrl_bypass_model_r <= 1'b0;
        timeout_cfg_cycles_r <= 32'h00000000;
        stale_cfg_cycles_r <= 32'h00000000;
        cmd_min_r <= 16'h0000;
        cmd_max_r <= 16'h0000;
        cmd_safe_r <= 16'h0000;
        seq_tx_r <= 16'h0000;
        meta_velocity_bucket_r <= 8'h00;
        meta_mode_r <= 4'h0;
        meta_env_flags_r <= 4'h0;
        meta_session_id_r <= 16'h0000;
        wb_dat_o_r <= 32'h00000000;
        wb_ack_o_r <= 1'b0;
        wb_err_o_r <= 1'b0;
    end else begin
        wb_dat_o_r <= read_data_next;
        wb_ack_o_r <= wb_access;
        wb_err_o_r <= wb_err_next;
        ctrl_clear_fault_r <= 1'b0;
        ctrl_request_start_r <= 1'b0;
        if (wb_write) begin
            case (wb_addr)
                8'h00: begin
                    if (wb_sel_i[0]) begin
                        ctrl_enable_r <= wb_dat_i[0];
                        ctrl_clear_fault_r <= wb_dat_i[1];
                        ctrl_arm_output_r <= wb_dat_i[2];
                        ctrl_request_start_r <= wb_dat_i[3];
                        ctrl_bypass_model_r <= wb_dat_i[4];
                    end
                end
                8'h08: begin
                    if (wb_sel_i[0]) timeout_cfg_cycles_r[7:0] <= wb_dat_i[7:0];
                    if (wb_sel_i[1]) timeout_cfg_cycles_r[15:8] <= wb_dat_i[15:8];
                    if (wb_sel_i[2]) timeout_cfg_cycles_r[23:16] <= wb_dat_i[23:16];
                    if (wb_sel_i[3]) timeout_cfg_cycles_r[31:24] <= wb_dat_i[31:24];
                end
                8'h0C: begin
                    if (wb_sel_i[0]) stale_cfg_cycles_r[7:0] <= wb_dat_i[7:0];
                    if (wb_sel_i[1]) stale_cfg_cycles_r[15:8] <= wb_dat_i[15:8];
                    if (wb_sel_i[2]) stale_cfg_cycles_r[23:16] <= wb_dat_i[23:16];
                    if (wb_sel_i[3]) stale_cfg_cycles_r[31:24] <= wb_dat_i[31:24];
                end
                8'h10: begin
                    if (wb_sel_i[0]) cmd_min_r[7:0] <= wb_dat_i[7:0];
                    if (wb_sel_i[1]) cmd_min_r[15:8] <= wb_dat_i[15:8];
                end
                8'h14: begin
                    if (wb_sel_i[0]) cmd_max_r[7:0] <= wb_dat_i[7:0];
                    if (wb_sel_i[1]) cmd_max_r[15:8] <= wb_dat_i[15:8];
                end
                8'h18: begin
                    if (wb_sel_i[0]) cmd_safe_r[7:0] <= wb_dat_i[7:0];
                    if (wb_sel_i[1]) cmd_safe_r[15:8] <= wb_dat_i[15:8];
                end
                8'h1C: begin
                    if (wb_sel_i[0]) seq_tx_r[7:0] <= wb_dat_i[7:0];
                    if (wb_sel_i[1]) seq_tx_r[15:8] <= wb_dat_i[15:8];
                end
                8'h24: begin
                    if (wb_sel_i[0]) meta_velocity_bucket_r <= wb_dat_i[7:0];
                    if (wb_sel_i[1]) begin
                        meta_mode_r <= wb_dat_i[11:8];
                        meta_env_flags_r <= wb_dat_i[15:12];
                    end
                    if (wb_sel_i[2]) meta_session_id_r[7:0] <= wb_dat_i[23:16];
                    if (wb_sel_i[3]) meta_session_id_r[15:8] <= wb_dat_i[31:24];
                end
                default: begin
                end
            endcase
        end
    end
end

endmodule
