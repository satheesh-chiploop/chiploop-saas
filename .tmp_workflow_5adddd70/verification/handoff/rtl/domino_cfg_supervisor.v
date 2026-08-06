module domino_cfg_supervisor (
    clk,
    rst_n,
    host_cfg_valid,
    host_cfg_write,
    host_cfg_addr,
    host_cfg_wdata,
    host_cfg_ready,
    host_cfg_rdata,
    host_cfg_rvalid,
    cfg_enable,
    cfg_freshness_timeout_cycles,
    cfg_request_timeout_cycles,
    cfg_actuator_min_limit,
    cfg_actuator_max_limit,
    cfg_safe_fallback_command_value,
    cfg_stream_velocity_low_limit,
    cfg_stream_velocity_high_limit,
    cfg_geometry_format_selector,
    cfg_fault_clear,
    cfg_mode_select_fallback_when_valid,
    cfg_fault,
    cfg_defaults_loaded
);
input clk;
input rst_n;
input host_cfg_valid;
input host_cfg_write;
input [7:0] host_cfg_addr;
input [31:0] host_cfg_wdata;
input host_cfg_ready;
output reg [31:0] host_cfg_rdata;
output reg host_cfg_rvalid;
output reg cfg_enable;
output reg [15:0] cfg_freshness_timeout_cycles;
output reg [15:0] cfg_request_timeout_cycles;
output reg [15:0] cfg_actuator_min_limit;
output reg [15:0] cfg_actuator_max_limit;
output reg [15:0] cfg_safe_fallback_command_value;
output reg [15:0] cfg_stream_velocity_low_limit;
output reg [15:0] cfg_stream_velocity_high_limit;
output reg [7:0] cfg_geometry_format_selector;
output reg cfg_fault_clear;
output reg cfg_mode_select_fallback_when_valid;
output reg cfg_fault;
input cfg_defaults_loaded;

localparam [7:0] REG_CTRL = 8'h00;
localparam [7:0] REG_STATUS = 8'h01;
localparam [7:0] REG_MODE = 8'h02;
localparam [7:0] REG_LIMITS = 8'h03;
localparam [7:0] REG_LIMITS_MSB = 8'h04;
localparam [7:0] REG_LIMITS2 = 8'h05;
localparam [7:0] REG_LIMITS2_MSB = 8'h06;
localparam [7:0] REG_FALLBACK_LSB = 8'h07;
localparam [7:0] REG_FALLBACK_MSB = 8'h08;
localparam [7:0] REG_ENV_LOW_LSB = 8'h09;
localparam [7:0] REG_ENV_LOW_MSB = 8'h0A;
localparam [7:0] REG_ENV_HIGH_LSB = 8'h0B;
localparam [7:0] REG_ENV_HIGH_MSB = 8'h0C;
localparam [7:0] REG_TIMEOUTS = 8'h0D;
localparam [7:0] REG_TIMEOUTS_MSB = 8'h0E;
localparam [7:0] REG_REQ_TIMEOUT = 8'h0F;
localparam [7:0] REG_REQ_TIMEOUT_MSB = 8'h10;
localparam [7:0] REG_GEOM_FMT = 8'h11;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        cfg_enable <= 1'b0;
        cfg_freshness_timeout_cycles <= 16'h0010;
        cfg_request_timeout_cycles <= 16'h0010;
        cfg_actuator_min_limit <= 16'h0000;
        cfg_actuator_max_limit <= 16'h0000;
        cfg_safe_fallback_command_value <= 16'h0000;
        cfg_stream_velocity_low_limit <= 16'h0014;
        cfg_stream_velocity_high_limit <= 16'h0037;
        cfg_geometry_format_selector <= 8'h00;
        cfg_fault_clear <= 1'b0;
        cfg_mode_select_fallback_when_valid <= 1'b1;
        cfg_fault <= 1'b0;
        host_cfg_rdata <= 32'h00000000;
        host_cfg_rvalid <= 1'b0;
    end else begin
        host_cfg_rvalid <= host_cfg_valid & ~host_cfg_write;
        if (host_cfg_valid && host_cfg_write) begin
            case (host_cfg_addr)
                REG_CTRL: begin
                    cfg_enable <= host_cfg_wdata[0];
                    cfg_fault_clear <= host_cfg_wdata[1];
                    cfg_mode_select_fallback_when_valid <= host_cfg_wdata[2];
                end
                REG_LIMITS: cfg_actuator_min_limit[7:0] <= host_cfg_wdata[7:0];
                REG_LIMITS_MSB: cfg_actuator_min_limit[15:8] <= host_cfg_wdata[7:0];
                REG_LIMITS2: cfg_actuator_max_limit[7:0] <= host_cfg_wdata[7:0];
                REG_LIMITS2_MSB: cfg_actuator_max_limit[15:8] <= host_cfg_wdata[7:0];
                REG_FALLBACK_LSB: cfg_safe_fallback_command_value[7:0] <= host_cfg_wdata[7:0];
                REG_FALLBACK_MSB: cfg_safe_fallback_command_value[15:8] <= host_cfg_wdata[7:0];
                REG_ENV_LOW_LSB: cfg_stream_velocity_low_limit[7:0] <= host_cfg_wdata[7:0];
                REG_ENV_LOW_MSB: cfg_stream_velocity_low_limit[15:8] <= host_cfg_wdata[7:0];
                REG_ENV_HIGH_LSB: cfg_stream_velocity_high_limit[7:0] <= host_cfg_wdata[7:0];
                REG_ENV_HIGH_MSB: cfg_stream_velocity_high_limit[15:8] <= host_cfg_wdata[7:0];
                REG_TIMEOUTS: cfg_freshness_timeout_cycles[7:0] <= host_cfg_wdata[7:0];
                REG_TIMEOUTS_MSB: cfg_freshness_timeout_cycles[15:8] <= host_cfg_wdata[7:0];
                REG_REQ_TIMEOUT: cfg_request_timeout_cycles[7:0] <= host_cfg_wdata[7:0];
                REG_REQ_TIMEOUT_MSB: cfg_request_timeout_cycles[15:8] <= host_cfg_wdata[7:0];
                REG_GEOM_FMT: cfg_geometry_format_selector <= host_cfg_wdata[7:0];
                default: begin
                end
            endcase
        end
        if (host_cfg_valid && !host_cfg_write) begin
            case (host_cfg_addr)
                REG_CTRL: host_cfg_rdata <= {29'h00000000, cfg_mode_select_fallback_when_valid, cfg_fault_clear, cfg_enable};
                REG_STATUS: host_cfg_rdata <= {24'h000000, cfg_fault, 7'h00};
                REG_MODE: host_cfg_rdata <= {26'h0000000, cfg_mode_select_fallback_when_valid, 1'b0, cfg_fault_clear, cfg_enable};
                REG_LIMITS: host_cfg_rdata <= {24'h000000, cfg_actuator_min_limit[7:0]};
                REG_LIMITS_MSB: host_cfg_rdata <= {24'h000000, cfg_actuator_min_limit[15:8]};
                REG_LIMITS2: host_cfg_rdata <= {24'h000000, cfg_actuator_max_limit[7:0]};
                REG_LIMITS2_MSB: host_cfg_rdata <= {24'h000000, cfg_actuator_max_limit[15:8]};
                REG_FALLBACK_LSB: host_cfg_rdata <= {24'h000000, cfg_safe_fallback_command_value[7:0]};
                REG_FALLBACK_MSB: host_cfg_rdata <= {24'h000000, cfg_safe_fallback_command_value[15:8]};
                REG_ENV_LOW_LSB: host_cfg_rdata <= {24'h000000, cfg_stream_velocity_low_limit[7:0]};
                REG_ENV_LOW_MSB: host_cfg_rdata <= {24'h000000, cfg_stream_velocity_low_limit[15:8]};
                REG_ENV_HIGH_LSB: host_cfg_rdata <= {24'h000000, cfg_stream_velocity_high_limit[7:0]};
                REG_ENV_HIGH_MSB: host_cfg_rdata <= {24'h000000, cfg_stream_velocity_high_limit[15:8]};
                REG_TIMEOUTS: host_cfg_rdata <= {24'h000000, cfg_freshness_timeout_cycles[7:0]};
                REG_TIMEOUTS_MSB: host_cfg_rdata <= {24'h000000, cfg_freshness_timeout_cycles[15:8]};
                REG_REQ_TIMEOUT: host_cfg_rdata <= {24'h000000, cfg_request_timeout_cycles[7:0]};
                REG_REQ_TIMEOUT_MSB: host_cfg_rdata <= {24'h000000, cfg_request_timeout_cycles[15:8]};
                REG_GEOM_FMT: host_cfg_rdata <= {24'h000000, cfg_geometry_format_selector};
                default: host_cfg_rdata <= 32'h00000000;
            endcase
        end
        if (cfg_defaults_loaded) begin
            cfg_fault <= cfg_fault & ~cfg_fault_clear;
        end else begin
            if (cfg_actuator_min_limit > cfg_actuator_max_limit) begin
                cfg_fault <= 1'b1;
            end
        end
    end
end
endmodule
