module adaptive_aero_control_top_mmio (
    clk,
    reset_n,
    wb_adr_i,
    wb_dat_i,
    wb_dat_o,
    wb_we_i,
    wb_stb_i,
    wb_cyc_i,
    wb_ack_o,
    wb_err_o,
    cfg_oper_en_min,
    cfg_oper_en_max,
    cfg_timeout_cycles,
    cfg_clamp_min,
    cfg_clamp_max,
    cfg_rate_limit_en,
    cfg_rate_limit_step,
    cfg_fallback_cmd,
    cfg_force_safe_mode,
    cfg_allow_multi_outstanding,
    cfg_request_issue,
    cfg_request_id,
    cfg_geometry_handle,
    cfg_flow_handle,
    cfg_timestamp,
    cfg_command_mode,
    cfg_status_flags,
    reg_version,
    reg_capabilities,
    reg_state,
    reg_fault_summary,
    reg_outstanding_req_id,
    reg_response_req_id,
    reg_last_accepted_cmd,
    reg_pending,
    reg_response_received,
    reg_stale_reject,
    reg_timeout_expired,
    reg_clamp_active,
    reg_fallback_active,
    reg_envelope_violation,
    reg_service_error,
    reg_irq_pulse
);

input clk;
input reset_n;
input [31:0] wb_adr_i;
input [31:0] wb_dat_i;
output [31:0] wb_dat_o;
input wb_we_i;
input wb_stb_i;
input wb_cyc_i;
output wb_ack_o;
output wb_err_o;

output [15:0] cfg_oper_en_min;
output [15:0] cfg_oper_en_max;
output [31:0] cfg_timeout_cycles;
output [15:0] cfg_clamp_min;
output [15:0] cfg_clamp_max;
output cfg_rate_limit_en;
output [15:0] cfg_rate_limit_step;
output [15:0] cfg_fallback_cmd;
output cfg_force_safe_mode;
output cfg_allow_multi_outstanding;
output cfg_request_issue;
output [7:0] cfg_request_id;
output [15:0] cfg_geometry_handle;
output [15:0] cfg_flow_handle;
output [31:0] cfg_timestamp;
output [3:0] cfg_command_mode;
output [7:0] cfg_status_flags;
output [31:0] reg_version;
output [31:0] reg_capabilities;
input [7:0] reg_state;
input [15:0] reg_fault_summary;
input [7:0] reg_outstanding_req_id;
input [7:0] reg_response_req_id;
input [15:0] reg_last_accepted_cmd;
input reg_pending;
input reg_response_received;
input reg_stale_reject;
input reg_timeout_expired;
input reg_clamp_active;
input reg_fallback_active;
input reg_envelope_violation;
input reg_service_error;
input reg_irq_pulse;

reg [15:0] r_oper_en_min;
reg [15:0] r_oper_en_max;
reg [31:0] r_timeout_cycles;
reg [15:0] r_clamp_min;
reg [15:0] r_clamp_max;
reg r_rate_limit_en;
reg [15:0] r_rate_limit_step;
reg [15:0] r_fallback_cmd;
reg r_force_safe_mode;
reg r_allow_multi_outstanding;
reg r_request_issue;
reg [7:0] r_request_id;
reg [15:0] r_geometry_handle;
reg [15:0] r_flow_handle;
reg [31:0] r_timestamp;
reg [3:0] r_command_mode;
reg [7:0] r_status_flags;
reg [31:0] wb_dat_o_r;
reg wb_ack_o_r;
reg wb_err_o_r;

wire access;
wire write_access;
wire read_access;
wire illegal_addr;
wire [7:0] addr_word;

assign access = wb_cyc_i & wb_stb_i;
assign write_access = access & wb_we_i;
assign read_access = access & ~wb_we_i;
assign addr_word = wb_adr_i[7:0];
assign illegal_addr = (addr_word != 8'h00) && (addr_word != 8'h04) && (addr_word != 8'h08) &&
                      (addr_word != 8'h0C) && (addr_word != 8'h10) && (addr_word != 8'h14) &&
                      (addr_word != 8'h18) && (addr_word != 8'h1C) && (addr_word != 8'h20) &&
                      (addr_word != 8'h24) && (addr_word != 8'h28) && (addr_word != 8'h2C) &&
                      (addr_word != 8'h30) && (addr_word != 8'h34) && (addr_word != 8'h38) &&
                      (addr_word != 8'h3C) && (addr_word != 8'h40) && (addr_word != 8'h44) &&
                      (addr_word != 8'h48);

assign wb_dat_o = wb_dat_o_r;
assign wb_ack_o = wb_ack_o_r;
assign wb_err_o = wb_err_o_r;

assign cfg_oper_en_min = r_oper_en_min;
assign cfg_oper_en_max = r_oper_en_max;
assign cfg_timeout_cycles = r_timeout_cycles;
assign cfg_clamp_min = r_clamp_min;
assign cfg_clamp_max = r_clamp_max;
assign cfg_rate_limit_en = r_rate_limit_en;
assign cfg_rate_limit_step = r_rate_limit_step;
assign cfg_fallback_cmd = r_fallback_cmd;
assign cfg_force_safe_mode = r_force_safe_mode;
assign cfg_allow_multi_outstanding = r_allow_multi_outstanding;
assign cfg_request_issue = r_request_issue;
assign cfg_request_id = r_request_id;
assign cfg_geometry_handle = r_geometry_handle;
assign cfg_flow_handle = r_flow_handle;
assign cfg_timestamp = r_timestamp;
assign cfg_command_mode = r_command_mode;
assign cfg_status_flags = r_status_flags;

assign reg_version = 32'h00010000;
assign reg_capabilities = 32'h0000001F;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        r_oper_en_min <= 16'h0000;
        r_oper_en_max <= 16'hFFFF;
        r_timeout_cycles <= 32'h0000C350;
        r_clamp_min <= 16'h0000;
        r_clamp_max <= 16'hFFFF;
        r_rate_limit_en <= 1'b0;
        r_rate_limit_step <= 16'h0010;
        r_fallback_cmd <= 16'h0000;
        r_force_safe_mode <= 1'b0;
        r_allow_multi_outstanding <= 1'b0;
        r_request_issue <= 1'b0;
        r_request_id <= 8'h00;
        r_geometry_handle <= 16'h0000;
        r_flow_handle <= 16'h0000;
        r_timestamp <= 32'h00000000;
        r_command_mode <= 4'h0;
        r_status_flags <= 8'h00;
        wb_dat_o_r <= 32'h00000000;
        wb_ack_o_r <= 1'b0;
        wb_err_o_r <= 1'b0;
    end else begin
        wb_ack_o_r <= access;
        wb_err_o_r <= access & illegal_addr;
        if (write_access) begin
            case (addr_word)
                8'h08: begin
                    r_request_issue <= wb_dat_i[0];
                    r_force_safe_mode <= wb_dat_i[1];
                    r_allow_multi_outstanding <= wb_dat_i[2];
                    r_rate_limit_en <= wb_dat_i[3];
                end
                8'h0C: r_oper_en_min <= wb_dat_i[15:0];
                8'h10: r_oper_en_max <= wb_dat_i[15:0];
                8'h14: r_timeout_cycles <= wb_dat_i;
                8'h18: r_clamp_min <= wb_dat_i[15:0];
                8'h1C: r_clamp_max <= wb_dat_i[15:0];
                8'h20: r_rate_limit_step <= wb_dat_i[15:0];
                8'h24: r_fallback_cmd <= wb_dat_i[15:0];
                8'h28: begin
                    r_request_issue <= wb_dat_i[0];
                    r_request_id <= wb_dat_i[15:8];
                    r_geometry_handle <= wb_dat_i[31:16];
                end
                8'h2C: begin
                    r_flow_handle <= wb_dat_i[15:0];
                    r_command_mode <= wb_dat_i[19:16];
                    r_status_flags <= wb_dat_i[31:24];
                end
                8'h30: r_timestamp <= wb_dat_i;
                default: begin
                end
            endcase
        end
        case (addr_word)
            8'h00: wb_dat_o_r <= reg_version;
            8'h04: wb_dat_o_r <= reg_capabilities;
            8'h08: wb_dat_o_r <= {28'h0000000, r_rate_limit_en, r_allow_multi_outstanding, r_force_safe_mode, r_request_issue};
            8'h0C: wb_dat_o_r <= {16'h0000, r_oper_en_min};
            8'h10: wb_dat_o_r <= {16'h0000, r_oper_en_max};
            8'h14: wb_dat_o_r <= r_timeout_cycles;
            8'h18: wb_dat_o_r <= {16'h0000, r_clamp_min};
            8'h1C: wb_dat_o_r <= {16'h0000, r_clamp_max};
            8'h20: wb_dat_o_r <= {16'h0000, r_rate_limit_step};
            8'h24: wb_dat_o_r <= {16'h0000, r_fallback_cmd};
            8'h28: wb_dat_o_r <= {8'h00, r_request_id, r_geometry_handle};
            8'h2C: wb_dat_o_r <= {r_status_flags, 4'h0, r_command_mode, r_flow_handle};
            8'h30: wb_dat_o_r <= r_timestamp;
            8'h34: wb_dat_o_r <= {16'h0000, reg_service_error, reg_envelope_violation, reg_fallback_active, reg_clamp_active, reg_timeout_expired, reg_stale_reject, reg_response_received, reg_pending, reg_state};
            8'h38: wb_dat_o_r <= {24'h000000, reg_outstanding_req_id};
            8'h3C: wb_dat_o_r <= {24'h000000, reg_response_req_id};
            8'h40: wb_dat_o_r <= {16'h0000, reg_last_accepted_cmd};
            8'h44: wb_dat_o_r <= {16'h0000, reg_fault_summary};
            8'h48: wb_dat_o_r <= {31'h00000000, reg_irq_pulse};
            default: wb_dat_o_r <= 32'h00000000;
        endcase
    end
end

endmodule
