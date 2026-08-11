module adaptive_aero_control_top_mmio (
    clk,
    reset,
    reg_cs,
    reg_we,
    reg_re,
    reg_addr,
    reg_wdata,
    reg_rdata,
    cfg_enable,
    cfg_mode,
    cfg_hold_last_valid,
    cfg_fallback_enable,
    cfg_heartbeat_enable,
    cfg_seq_reset,
    cfg_signed_clamp,
    cfg_queue_depth,
    cfg_service_flags,
    cfg_timeout_cycles,
    cfg_heartbeat_timeout_cycles,
    cfg_act0_min,
    cfg_act0_max,
    cfg_act1_min,
    cfg_act1_max,
    cfg_act2_min,
    cfg_act2_max,
    cfg_act3_min,
    cfg_act3_max,
    cfg_mode_context,
    cfg_operating_point_tag,
    cfg_velocity_tag,
    cfg_geometry_id,
    cfg_velocity_setpoint,
    cfg_age_basis,
    status_fault_summary,
    status_heartbeat,
    status_accepted_req_count,
    status_accepted_rsp_count,
    status_rejected_rsp_count,
    status_fallback_entry_count
);

input clk;
input reset;
input reg_cs;
input reg_we;
input reg_re;
input [3:0] reg_addr;
input [63:0] reg_wdata;
output [63:0] reg_rdata;
output reg cfg_enable;
output reg [2:0] cfg_mode;
output reg cfg_hold_last_valid;
output reg cfg_fallback_enable;
output reg cfg_heartbeat_enable;
output reg cfg_seq_reset;
output reg cfg_signed_clamp;
output reg [2:0] cfg_queue_depth;
output reg [7:0] cfg_service_flags;
output reg [31:0] cfg_timeout_cycles;
output reg [31:0] cfg_heartbeat_timeout_cycles;
output reg [15:0] cfg_act0_min;
output reg [15:0] cfg_act0_max;
output reg [15:0] cfg_act1_min;
output reg [15:0] cfg_act1_max;
output reg [15:0] cfg_act2_min;
output reg [15:0] cfg_act2_max;
output reg [15:0] cfg_act3_min;
output reg [15:0] cfg_act3_max;
output reg [3:0] cfg_mode_context;
output reg [11:0] cfg_operating_point_tag;
output reg [15:0] cfg_velocity_tag;
output reg [31:0] cfg_geometry_id;
output reg [31:0] cfg_velocity_setpoint;
output reg [31:0] cfg_age_basis;
input [7:0] status_fault_summary;
input [7:0] status_heartbeat;
input [15:0] status_accepted_req_count;
input [15:0] status_accepted_rsp_count;
input [7:0] status_rejected_rsp_count;
input [7:0] status_fallback_entry_count;
reg [63:0] reg_rdata_r;
assign reg_rdata = reg_rdata_r;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        cfg_enable <= 1'b0;
        cfg_mode <= 3'b000;
        cfg_hold_last_valid <= 1'b0;
        cfg_fallback_enable <= 1'b1;
        cfg_heartbeat_enable <= 1'b1;
        cfg_seq_reset <= 1'b0;
        cfg_signed_clamp <= 1'b0;
        cfg_queue_depth <= 3'b001;
        cfg_service_flags <= 8'h00;
        cfg_timeout_cycles <= 32'd1000000;
        cfg_heartbeat_timeout_cycles <= 32'd2000000;
        cfg_act0_min <= 16'd0;
        cfg_act0_max <= 16'd65535;
        cfg_act1_min <= 16'd0;
        cfg_act1_max <= 16'd65535;
        cfg_act2_min <= 16'd0;
        cfg_act2_max <= 16'd65535;
        cfg_act3_min <= 16'd0;
        cfg_act3_max <= 16'd65535;
        cfg_mode_context <= 4'h0;
        cfg_operating_point_tag <= 12'h000;
        cfg_velocity_tag <= 16'h0000;
        cfg_geometry_id <= 32'h00000000;
        cfg_velocity_setpoint <= 32'h00000000;
        cfg_age_basis <= 32'h00000000;
    end else begin
        cfg_seq_reset <= 1'b0;
        if (reg_cs && reg_we) begin
            case (reg_addr)
                4'h0: begin
                    cfg_enable <= reg_wdata[0];
                    cfg_mode <= reg_wdata[3:1];
                    cfg_hold_last_valid <= reg_wdata[4];
                    cfg_fallback_enable <= reg_wdata[5];
                    cfg_heartbeat_enable <= reg_wdata[6];
                    cfg_seq_reset <= reg_wdata[7];
                    cfg_signed_clamp <= reg_wdata[8];
                    cfg_queue_depth <= reg_wdata[11:9];
                    cfg_service_flags <= reg_wdata[23:16];
                end
                4'h1: begin
                    cfg_timeout_cycles <= reg_wdata[31:0];
                    cfg_heartbeat_timeout_cycles <= reg_wdata[63:32];
                end
                4'h2: begin
                    cfg_act0_min <= reg_wdata[15:0];
                    cfg_act0_max <= reg_wdata[31:16];
                    cfg_act1_min <= reg_wdata[47:32];
                    cfg_act1_max <= reg_wdata[63:48];
                end
                4'h3: begin
                    cfg_act2_min <= reg_wdata[15:0];
                    cfg_act2_max <= reg_wdata[31:16];
                    cfg_act3_min <= reg_wdata[47:32];
                    cfg_act3_max <= reg_wdata[63:48];
                end
                4'h5: begin
                    cfg_mode_context <= reg_wdata[3:0];
                    cfg_operating_point_tag <= reg_wdata[15:4];
                    cfg_velocity_tag <= reg_wdata[31:16];
                    cfg_geometry_id <= reg_wdata[63:32];
                end
                4'h6: begin
                    cfg_velocity_setpoint <= reg_wdata[31:0];
                    cfg_age_basis <= reg_wdata[63:32];
                end
                default: begin
                end
            endcase
        end
    end
end

always @(*) begin
    reg_rdata_r = 64'h0000000000000000;
    case (reg_addr)
        4'h0: reg_rdata_r = {39'b0, cfg_service_flags, 5'h00, cfg_queue_depth, cfg_signed_clamp, cfg_seq_reset, cfg_heartbeat_enable, cfg_fallback_enable, cfg_hold_last_valid, cfg_mode, cfg_enable};
        4'h1: reg_rdata_r = {cfg_heartbeat_timeout_cycles, cfg_timeout_cycles};
        4'h2: reg_rdata_r = {cfg_act1_max, cfg_act1_min, cfg_act0_max, cfg_act0_min};
        4'h3: reg_rdata_r = {cfg_act3_max, cfg_act3_min, cfg_act2_max, cfg_act2_min};
        4'h4: reg_rdata_r = {status_fallback_entry_count, status_rejected_rsp_count, status_accepted_rsp_count, status_accepted_req_count, status_heartbeat, status_fault_summary};
        4'h5: reg_rdata_r = {cfg_geometry_id, cfg_velocity_tag, cfg_operating_point_tag, cfg_mode_context};
        4'h6: reg_rdata_r = {cfg_age_basis, cfg_velocity_setpoint};
        default: reg_rdata_r = 64'h0000000000000000;
    endcase
end

endmodule
