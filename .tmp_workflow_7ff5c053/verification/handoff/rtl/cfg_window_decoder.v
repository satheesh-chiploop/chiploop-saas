module cfg_window_decoder (
    clk,
    rst_n,
    cfg_addr,
    cfg_wdata,
    cfg_we,
    cfg_re,
    cfg_rdata,
    cfg_enable,
    operating_velocity_mps,
    response_timeout_cycles,
    request_age_limit_cycles,
    actuator_min_limit,
    actuator_max_limit,
    safe_fallback_setpoint,
    mode_select,
    geometry_ref_id,
    config_error
);
    input clk;
    input rst_n;
    input [5:0] cfg_addr;
    input [63:0] cfg_wdata;
    input cfg_we;
    input cfg_re;
    output [63:0] cfg_rdata;
    output cfg_enable;
    output [15:0] operating_velocity_mps;
    output [15:0] response_timeout_cycles;
    output [15:0] request_age_limit_cycles;
    output [15:0] actuator_min_limit;
    output [15:0] actuator_max_limit;
    output [15:0] safe_fallback_setpoint;
    output [3:0] mode_select;
    output [7:0] geometry_ref_id;
    output config_error;

    reg [63:0] cfg0_reg;
    reg [63:0] cfg1_reg;
    reg cfg_enable_r;
    reg [15:0] operating_velocity_mps_r;
    reg [15:0] response_timeout_cycles_r;
    reg [15:0] request_age_limit_cycles_r;
    reg [15:0] actuator_min_limit_r;
    reg [15:0] actuator_max_limit_r;
    reg [15:0] safe_fallback_setpoint_r;
    reg [3:0] mode_select_r;
    reg [7:0] geometry_ref_id_r;
    reg config_error_r;
    reg [63:0] cfg_rdata_r;
    reg [63:0] cfg_rdata_next;

    assign cfg_rdata = cfg_rdata_r;
    assign cfg_enable = cfg_enable_r;
    assign operating_velocity_mps = operating_velocity_mps_r;
    assign response_timeout_cycles = response_timeout_cycles_r;
    assign request_age_limit_cycles = request_age_limit_cycles_r;
    assign actuator_min_limit = actuator_min_limit_r;
    assign actuator_max_limit = actuator_max_limit_r;
    assign safe_fallback_setpoint = safe_fallback_setpoint_r;
    assign mode_select = mode_select_r;
    assign geometry_ref_id = geometry_ref_id_r;
    assign config_error = config_error_r;

    always @(*) begin
        cfg_rdata_next = 64'h0000000000000000;
        case (cfg_addr)
            6'h00: cfg_rdata_next = cfg0_reg;
            6'h01: cfg_rdata_next = cfg1_reg;
            6'h02: cfg_rdata_next = {2'b0, request_age_limit_cycles_r, response_timeout_cycles_r[15:0], operating_velocity_mps_r[15:0], geometry_ref_id_r[7:0], mode_select_r[3:0], config_error_r, cfg_enable_r};
            6'h03: cfg_rdata_next = 64'h0000000000000000;
            6'h04: cfg_rdata_next = 64'h0000000000000000;
            6'h05: cfg_rdata_next = {47'h0, 1'b1, 1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b1, 10'b0};
            default: cfg_rdata_next = 64'h0000000000000000;
        endcase
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            cfg0_reg <= 64'h0000000000000000;
            cfg1_reg <= 64'h0000000000000000;
            cfg_enable_r <= 1'b0;
            operating_velocity_mps_r <= 16'd20;
            response_timeout_cycles_r <= 16'd1000;
            request_age_limit_cycles_r <= 16'd1000;
            actuator_min_limit_r <= 16'd0;
            actuator_max_limit_r <= 16'd65535;
            safe_fallback_setpoint_r <= 16'd0;
            mode_select_r <= 4'd0;
            geometry_ref_id_r <= 8'd0;
            config_error_r <= 1'b0;
            cfg_rdata_r <= 64'h0000000000000000;
        end else begin
            cfg_rdata_r <= cfg_rdata_next;
            if (cfg_we) begin
                case (cfg_addr)
                    6'h00: begin
                        cfg0_reg <= cfg_wdata;
                        cfg_enable_r <= cfg_wdata[0];
                        mode_select_r <= cfg_wdata[4:1];
                        geometry_ref_id_r <= cfg_wdata[12:5];
                        operating_velocity_mps_r <= cfg_wdata[28:13];
                        response_timeout_cycles_r <= cfg_wdata[44:29];
                        request_age_limit_cycles_r <= cfg_wdata[60:45];
                    end
                    6'h01: begin
                        cfg1_reg <= cfg_wdata;
                        actuator_min_limit_r <= cfg_wdata[15:0];
                        actuator_max_limit_r <= cfg_wdata[31:16];
                        safe_fallback_setpoint_r <= cfg_wdata[47:32];
                    end
                    default: begin
                    end
                endcase
            end
            config_error_r <= (operating_velocity_mps_r < 16'd20) || (operating_velocity_mps_r > 16'd55) ||
                              (actuator_min_limit_r > actuator_max_limit_r) ||
                              (safe_fallback_setpoint_r < actuator_min_limit_r) ||
                              (safe_fallback_setpoint_r > actuator_max_limit_r) ||
                              (mode_select_r > 4'd15);
        end
    end
endmodule
