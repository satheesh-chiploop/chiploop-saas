module adaptive_aero_control_csr_mmio (
    input clk,
    input reset_n,
    input [7:0] mmio_addr,
    input [31:0] mmio_wdata,
    input mmio_valid,
    input mmio_write,
    output [31:0] mmio_rdata,
    output mmio_ready,
    output reg cfg_enable,
    output reg [2:0] cfg_mode_select,
    output reg [15:0] cfg_timeout_limit,
    output reg [15:0] cfg_stale_age_limit,
    output reg [15:0] cfg_actuator_min,
    output reg [15:0] cfg_actuator_max,
    output reg [15:0] cfg_rate_limit,
    output reg [15:0] cfg_sequence_seed,
    output reg cfg_status_clear,
    output reg cfg_pipelined_mode,
    output reg [15:0] cfg_safe_fallback_cmd,
    output reg [15:0] cfg_nominal_stream_velocity,
    output reg [15:0] cfg_geometry_descriptor_id,
    input [7:0] status_code,
    input [7:0] fault_flags,
    input [15:0] request_counter,
    input [15:0] response_counter,
    input [7:0] current_state,
    input [15:0] debug_counter0,
    input [15:0] debug_counter1
);

reg [31:0] mmio_rdata_r;
reg mmio_ready_r;
reg [31:0] ctrl_reg;
reg [31:0] timeout_reg;
reg [31:0] actuator_limits_reg;
reg [31:0] rates_seed_reg;
reg [31:0] target_reg;
reg [31:0] geometry_reg;
reg [31:0] fault_clear_reg;

assign mmio_rdata = mmio_rdata_r;
assign mmio_ready = mmio_ready_r;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        ctrl_reg <= 32'h00000000;
        timeout_reg <= 32'h00000000;
        actuator_limits_reg <= 32'hFFFF0000;
        rates_seed_reg <= 32'h00000000;
        target_reg <= 32'h00000000;
        geometry_reg <= 32'h00000000;
        fault_clear_reg <= 32'h00000000;
        cfg_enable <= 1'b0;
        cfg_mode_select <= 3'b000;
        cfg_timeout_limit <= 16'h0000;
        cfg_stale_age_limit <= 16'h0000;
        cfg_actuator_min <= 16'h0000;
        cfg_actuator_max <= 16'hFFFF;
        cfg_rate_limit <= 16'h0000;
        cfg_sequence_seed <= 16'h0000;
        cfg_status_clear <= 1'b0;
        cfg_pipelined_mode <= 1'b0;
        cfg_safe_fallback_cmd <= 16'h0000;
        cfg_nominal_stream_velocity <= 16'h0000;
        cfg_geometry_descriptor_id <= 16'h0000;
        mmio_ready_r <= 1'b0;
        mmio_rdata_r <= 32'h00000000;
    end else begin
        mmio_ready_r <= 1'b0;
        cfg_status_clear <= 1'b0;
        if (mmio_valid) begin
            mmio_ready_r <= 1'b1;
            if (mmio_write) begin
                case (mmio_addr)
                    8'h00: begin
                        ctrl_reg <= mmio_wdata;
                        cfg_enable <= mmio_wdata[0];
                        cfg_mode_select <= mmio_wdata[3:1];
                        cfg_pipelined_mode <= mmio_wdata[4];
                        cfg_status_clear <= mmio_wdata[5];
                        if (mmio_wdata[5]) fault_clear_reg <= mmio_wdata;
                    end
                    8'h01: begin
                        timeout_reg <= mmio_wdata;
                        cfg_timeout_limit <= mmio_wdata[15:0];
                        cfg_stale_age_limit <= mmio_wdata[31:16];
                    end
                    8'h02: begin
                        actuator_limits_reg <= mmio_wdata;
                        cfg_actuator_min <= mmio_wdata[15:0];
                        cfg_actuator_max <= mmio_wdata[31:16];
                    end
                    8'h03: begin
                        rates_seed_reg <= mmio_wdata;
                        cfg_rate_limit <= mmio_wdata[15:0];
                        cfg_sequence_seed <= mmio_wdata[31:16];
                    end
                    8'h04: begin
                        target_reg <= mmio_wdata;
                        cfg_safe_fallback_cmd <= mmio_wdata[15:0];
                        cfg_nominal_stream_velocity <= mmio_wdata[31:16];
                    end
                    8'h05: begin
                        geometry_reg <= mmio_wdata;
                        cfg_geometry_descriptor_id <= mmio_wdata[15:0];
                    end
                    8'h14: begin
                        fault_clear_reg <= mmio_wdata;
                        cfg_status_clear <= mmio_wdata[0];
                    end
                    default: begin
                    end
                endcase
            end
            case (mmio_addr)
                8'h00: mmio_rdata_r <= ctrl_reg;
                8'h01: mmio_rdata_r <= timeout_reg;
                8'h02: mmio_rdata_r <= actuator_limits_reg;
                8'h03: mmio_rdata_r <= rates_seed_reg;
                8'h04: mmio_rdata_r <= target_reg;
                8'h05: mmio_rdata_r <= geometry_reg;
                8'h10: mmio_rdata_r <= {request_counter[7:0], response_counter[7:0], fault_flags, status_code};
                8'h11: mmio_rdata_r <= {24'h000000, current_state};
                8'h12: mmio_rdata_r <= {16'h0000, debug_counter0};
                8'h13: mmio_rdata_r <= {16'h0000, debug_counter1};
                8'h14: mmio_rdata_r <= fault_clear_reg;
                default: mmio_rdata_r <= 32'h00000000;
            endcase
        end
    end
end

endmodule
