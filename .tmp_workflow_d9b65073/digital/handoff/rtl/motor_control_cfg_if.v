module motor_control_cfg_if (
    input         clk,
    input         reset_n,
    input         cfg_valid,
    output reg    cfg_ready,
    input  [15:0] cfg_addr,
    input         cfg_we,
    input  [31:0] cfg_wdata,
    output reg [31:0] cfg_rdata,
    output reg    cfg_rvalid,
    output reg    host_go_start,
    output reg    host_clear_faults,
    output reg    host_emergency_stop,
    output reg    host_done_mode_latch,
    output reg [15:0] cfg_sequence_num,
    output reg [15:0] cfg_geometry_id,
    output reg [31:0] cfg_flow_condition,
    output reg [15:0] cfg_timeout_budget,
    output reg [15:0] cfg_freshness_limit,
    output reg [15:0] cfg_cmd_min,
    output reg [15:0] cfg_cmd_max,
    output reg [7:0] cfg_policy,
    output reg [31:0] cfg_safe_fallback_cfg,
    input  [31:0] status_i
);

reg [7:0] ctrl0;
reg [7:0] ctrl1;
reg [7:0] ctrl2;
reg [7:0] ctrl3;
reg [7:0] ctrl4;
reg [7:0] ctrl5;
reg [7:0] ctrl6;
reg [7:0] ctrl7;
reg [7:0] ctrl8;
reg [7:0] ctrl9;
reg [7:0] ctrl10;
reg [7:0] ctrl11;
reg [7:0] ctrl12;
reg [7:0] ctrl13;
reg [7:0] ctrl14;
reg [7:0] ctrl15;
reg [7:0] ctrl16;
reg [7:0] ctrl17;
reg [7:0] ctrl18;
reg [7:0] ctrl19;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        cfg_ready <= 1'b0;
        cfg_rdata <= 32'h00000000;
        cfg_rvalid <= 1'b0;
        host_go_start <= 1'b0;
        host_clear_faults <= 1'b0;
        host_emergency_stop <= 1'b0;
        host_done_mode_latch <= 1'b0;
        ctrl0 <= 8'h00; ctrl1 <= 8'h00; ctrl2 <= 8'h00; ctrl3 <= 8'h00;
        ctrl4 <= 8'h00; ctrl5 <= 8'h00; ctrl6 <= 8'h00; ctrl7 <= 8'h00;
        ctrl8 <= 8'h00; ctrl9 <= 8'h00; ctrl10 <= 8'h00; ctrl11 <= 8'h00;
        ctrl12 <= 8'h00; ctrl13 <= 8'h00; ctrl14 <= 8'h00; ctrl15 <= 8'hff;
        ctrl16 <= 8'h00; ctrl17 <= 8'h00; ctrl18 <= 8'h00; ctrl19 <= 8'h00;
        cfg_sequence_num <= 16'h0000;
        cfg_geometry_id <= 16'h0000;
        cfg_flow_condition <= 32'h00000000;
        cfg_timeout_budget <= 16'h0000;
        cfg_freshness_limit <= 16'h0000;
        cfg_cmd_min <= 16'h0000;
        cfg_cmd_max <= 16'h00ff;
        cfg_policy <= 8'h00;
        cfg_safe_fallback_cfg <= 32'h00000000;
    end else begin
        cfg_ready <= cfg_valid;
        cfg_rvalid <= cfg_valid & ~cfg_we;
        host_go_start <= 1'b0;
        host_clear_faults <= 1'b0;
        host_emergency_stop <= 1'b0;
        host_done_mode_latch <= 1'b0;
        if (cfg_valid && cfg_we) begin
            case (cfg_addr[7:0])
                8'h00: begin ctrl0 <= cfg_wdata[7:0]; host_go_start <= cfg_wdata[0]; host_clear_faults <= cfg_wdata[1]; host_emergency_stop <= cfg_wdata[2]; host_done_mode_latch <= cfg_wdata[3]; end
                8'h01: ctrl1 <= cfg_wdata[7:0];
                8'h02: ctrl2 <= cfg_wdata[7:0];
                8'h03: ctrl3 <= cfg_wdata[7:0];
                8'h04: ctrl4 <= cfg_wdata[7:0];
                8'h05: ctrl5 <= cfg_wdata[7:0];
                8'h06: ctrl6 <= cfg_wdata[7:0];
                8'h07: ctrl7 <= cfg_wdata[7:0];
                8'h08: ctrl8 <= cfg_wdata[7:0];
                8'h09: ctrl9 <= cfg_wdata[7:0];
                8'h0a: ctrl10 <= cfg_wdata[7:0];
                8'h0b: ctrl11 <= cfg_wdata[7:0];
                8'h0c: ctrl12 <= cfg_wdata[7:0];
                8'h0d: ctrl13 <= cfg_wdata[7:0];
                8'h0e: ctrl14 <= cfg_wdata[7:0];
                8'h0f: ctrl15 <= cfg_wdata[7:0];
                8'h10: ctrl16 <= cfg_wdata[7:0];
                8'h11: ctrl17 <= cfg_wdata[7:0];
                8'h12: ctrl18 <= cfg_wdata[7:0];
                8'h13: ctrl19 <= cfg_wdata[7:0];
                default: ;
            endcase
        end
        if (cfg_valid && !cfg_we) begin
            case (cfg_addr[7:0])
                8'h00: cfg_rdata <= {24'h000000, ctrl0};
                8'h01: cfg_rdata <= {24'h000000, ctrl1};
                8'h02: cfg_rdata <= {24'h000000, ctrl2};
                8'h03: cfg_rdata <= {24'h000000, ctrl3};
                8'h04: cfg_rdata <= {24'h000000, ctrl4};
                8'h05: cfg_rdata <= {24'h000000, ctrl5};
                8'h06: cfg_rdata <= {24'h000000, ctrl6};
                8'h07: cfg_rdata <= {24'h000000, ctrl7};
                8'h08: cfg_rdata <= {24'h000000, ctrl8};
                8'h09: cfg_rdata <= {24'h000000, ctrl9};
                8'h0a: cfg_rdata <= {24'h000000, ctrl10};
                8'h0b: cfg_rdata <= {24'h000000, ctrl11};
                8'h0c: cfg_rdata <= {24'h000000, ctrl12};
                8'h0d: cfg_rdata <= {24'h000000, ctrl13};
                8'h0e: cfg_rdata <= {24'h000000, ctrl14};
                8'h0f: cfg_rdata <= {24'h000000, ctrl15};
                8'h10: cfg_rdata <= {24'h000000, ctrl16};
                8'h11: cfg_rdata <= {24'h000000, ctrl17};
                8'h12: cfg_rdata <= {24'h000000, ctrl18};
                8'h13: cfg_rdata <= {24'h000000, ctrl19};
                8'h20: cfg_rdata <= status_i;
                8'h21: cfg_rdata <= {28'h0000000, status_i[3], status_i[2], status_i[1], status_i[0]};
                default: cfg_rdata <= 32'h00000000;
            endcase
        end
        cfg_sequence_num <= {ctrl2, ctrl1};
        cfg_geometry_id <= {ctrl4, ctrl3};
        cfg_flow_condition <= {ctrl8, ctrl7, ctrl6, ctrl5};
        cfg_timeout_budget <= {ctrl10, ctrl9};
        cfg_freshness_limit <= {ctrl12, ctrl11};
        cfg_cmd_min <= {ctrl14, ctrl13};
        cfg_cmd_max <= {ctrl16, ctrl15};
        cfg_policy <= ctrl17;
        cfg_safe_fallback_cfg <= {ctrl19, ctrl18, ctrl17, ctrl16};
    end
end

endmodule
