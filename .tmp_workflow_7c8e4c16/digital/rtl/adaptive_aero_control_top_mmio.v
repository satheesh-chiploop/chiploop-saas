module adaptive_aero_control_top_mmio (
    clk,
    rst_n,
    cfg_addr,
    cfg_wdata,
    cfg_rdata,
    cfg_valid,
    cfg_write,
    cfg_ready,
    cfg_enable,
    cfg_safe_fallback_select,
    cfg_max_cmd_pos,
    cfg_min_cmd_pos,
    cfg_max_cmd_rate,
    cfg_stale_timeout_cycles,
    cfg_response_timeout_cycles,
    cfg_sequence_expected,
    cfg_stream_velocity_setpoint,
    cfg_fault_mask,
    status_busy_i,
    status_accepted_i,
    status_rejected_stale_i,
    status_rejected_seq_i,
    status_timeout_i,
    status_fallback_active_i,
    status_clamped_i,
    status_fault_summary_i
);

input clk;
input rst_n;
input [63:0] cfg_addr;
input [63:0] cfg_wdata;
output [63:0] cfg_rdata;
input cfg_valid;
input cfg_write;
output cfg_ready;
output cfg_enable;
output cfg_safe_fallback_select;
output [63:0] cfg_max_cmd_pos;
output [63:0] cfg_min_cmd_pos;
output [63:0] cfg_max_cmd_rate;
output [63:0] cfg_stale_timeout_cycles;
output [63:0] cfg_response_timeout_cycles;
output [63:0] cfg_sequence_expected;
output [63:0] cfg_stream_velocity_setpoint;
output [63:0] cfg_fault_mask;
input status_busy_i;
input status_accepted_i;
input status_rejected_stale_i;
input status_rejected_seq_i;
input status_timeout_i;
input status_fallback_active_i;
input status_clamped_i;
input status_fault_summary_i;

reg [63:0] cfg_rdata_r;
reg cfg_ready_r;
reg cfg_enable_r;
reg cfg_safe_fallback_select_r;
reg [63:0] cfg_max_cmd_pos_r;
reg [63:0] cfg_min_cmd_pos_r;
reg [63:0] cfg_max_cmd_rate_r;
reg [63:0] cfg_stale_timeout_cycles_r;
reg [63:0] cfg_response_timeout_cycles_r;
reg [63:0] cfg_sequence_expected_r;
reg [63:0] cfg_stream_velocity_setpoint_r;
reg [63:0] cfg_fault_mask_r;
reg [63:0] status_shadow_r;

wire [63:0] read_data_mux;

assign cfg_rdata = cfg_rdata_r;
assign cfg_ready = cfg_ready_r;
assign cfg_enable = cfg_enable_r;
assign cfg_safe_fallback_select = cfg_safe_fallback_select_r;
assign cfg_max_cmd_pos = cfg_max_cmd_pos_r;
assign cfg_min_cmd_pos = cfg_min_cmd_pos_r;
assign cfg_max_cmd_rate = cfg_max_cmd_rate_r;
assign cfg_stale_timeout_cycles = cfg_stale_timeout_cycles_r;
assign cfg_response_timeout_cycles = cfg_response_timeout_cycles_r;
assign cfg_sequence_expected = cfg_sequence_expected_r;
assign cfg_stream_velocity_setpoint = cfg_stream_velocity_setpoint_r;
assign cfg_fault_mask = cfg_fault_mask_r;
assign read_data_mux = cfg_rdata_r;

always @(*) begin
    cfg_ready_r = cfg_valid;
    cfg_rdata_r = 64'h0000000000000000;
    case (cfg_addr)
        64'h0000000000000000: cfg_rdata_r = {62'h0000000000000000, cfg_safe_fallback_select_r, cfg_enable_r};
        64'h0000000000000008: cfg_rdata_r = cfg_max_cmd_pos_r;
        64'h0000000000000010: cfg_rdata_r = cfg_min_cmd_pos_r;
        64'h0000000000000018: cfg_rdata_r = cfg_max_cmd_rate_r;
        64'h0000000000000020: cfg_rdata_r = cfg_stale_timeout_cycles_r;
        64'h0000000000000028: cfg_rdata_r = cfg_response_timeout_cycles_r;
        64'h0000000000000030: cfg_rdata_r = cfg_sequence_expected_r;
        64'h0000000000000038: cfg_rdata_r = cfg_stream_velocity_setpoint_r;
        64'h0000000000000040: cfg_rdata_r = cfg_fault_mask_r;
        64'h0000000000000048: cfg_rdata_r = status_shadow_r;
        default: cfg_rdata_r = 64'h0000000000000000;
    endcase
end

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        cfg_enable_r <= 1'b0;
        cfg_safe_fallback_select_r <= 1'b0;
        cfg_max_cmd_pos_r <= 64'h0000000000000000;
        cfg_min_cmd_pos_r <= 64'h0000000000000000;
        cfg_max_cmd_rate_r <= 64'h0000000000000000;
        cfg_stale_timeout_cycles_r <= 64'h0000000000000000;
        cfg_response_timeout_cycles_r <= 64'h0000000000000000;
        cfg_sequence_expected_r <= 64'h0000000000000000;
        cfg_stream_velocity_setpoint_r <= 64'h0000000000000000;
        cfg_fault_mask_r <= 64'h0000000000000000;
        status_shadow_r <= 64'h0000000000000000;
    end else begin
        status_shadow_r[0] <= status_busy_i;
        status_shadow_r[1] <= status_accepted_i;
        status_shadow_r[2] <= status_rejected_stale_i;
        status_shadow_r[3] <= status_rejected_seq_i;
        status_shadow_r[4] <= status_timeout_i;
        status_shadow_r[5] <= status_fallback_active_i;
        status_shadow_r[6] <= status_clamped_i;
        status_shadow_r[7] <= status_fault_summary_i;
        status_shadow_r[63:8] <= 56'h00000000000000;
        if (cfg_valid && cfg_write) begin
            case (cfg_addr)
                64'h0000000000000000: begin
                    cfg_enable_r <= cfg_wdata[0];
                    cfg_safe_fallback_select_r <= cfg_wdata[1];
                end
                64'h0000000000000008: cfg_max_cmd_pos_r <= cfg_wdata;
                64'h0000000000000010: cfg_min_cmd_pos_r <= cfg_wdata;
                64'h0000000000000018: cfg_max_cmd_rate_r <= cfg_wdata;
                64'h0000000000000020: cfg_stale_timeout_cycles_r <= cfg_wdata;
                64'h0000000000000028: cfg_response_timeout_cycles_r <= cfg_wdata;
                64'h0000000000000030: cfg_sequence_expected_r <= cfg_wdata;
                64'h0000000000000038: cfg_stream_velocity_setpoint_r <= cfg_wdata;
                64'h0000000000000040: cfg_fault_mask_r <= cfg_wdata;
                default: begin
                end
            endcase
        end
    end
end

endmodule
