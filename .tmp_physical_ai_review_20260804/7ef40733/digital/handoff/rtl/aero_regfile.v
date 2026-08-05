module aero_regfile(
    clk,
    rst_n,
    host_reg_wr_valid,
    host_reg_rd_valid,
    host_reg_ready,
    host_reg_addr,
    host_reg_wdata,
    host_reg_rdata,
    host_reg_rvalid,
    cfg_enable,
    cfg_stream_velocity_mps_setpoint,
    cfg_velocity_min_limit,
    cfg_velocity_max_limit,
    cfg_actuator_min_limit,
    cfg_actuator_max_limit,
    cfg_actuator_safe_position,
    cfg_command_timeout_cycles,
    cfg_max_slew_rate,
    cfg_geometry_format_id,
    cfg_geometry_source_id,
    cfg_geometry_version,
    cfg_clear_faults,
    status_current_state,
    status_last_fault_code,
    status_stale_reject_count,
    status_clamp_event_count,
    status_fallback_active,
    status_last_accepted_seq,
    status_last_response_age,
    status_request_inflight,
    status_model_response_valid_seen
);
input clk;
input rst_n;
input host_reg_wr_valid;
input host_reg_rd_valid;
output host_reg_ready;
input [7:0] host_reg_addr;
input [31:0] host_reg_wdata;
output [31:0] host_reg_rdata;
output host_reg_rvalid;
output cfg_enable;
output [15:0] cfg_stream_velocity_mps_setpoint;
output [15:0] cfg_velocity_min_limit;
output [15:0] cfg_velocity_max_limit;
output [15:0] cfg_actuator_min_limit;
output [15:0] cfg_actuator_max_limit;
output [15:0] cfg_actuator_safe_position;
output [15:0] cfg_command_timeout_cycles;
output [15:0] cfg_max_slew_rate;
output [7:0] cfg_geometry_format_id;
output [7:0] cfg_geometry_source_id;
output [15:0] cfg_geometry_version;
output cfg_clear_faults;
input [3:0] status_current_state;
input [3:0] status_last_fault_code;
input [15:0] status_stale_reject_count;
input [15:0] status_clamp_event_count;
input status_fallback_active;
input [15:0] status_last_accepted_seq;
input [15:0] status_last_response_age;
input status_request_inflight;
input status_model_response_valid_seen;
reg host_reg_ready;
reg [31:0] host_reg_rdata;
reg host_reg_rvalid;
reg cfg_enable;
reg [15:0] cfg_stream_velocity_mps_setpoint;
reg [15:0] cfg_velocity_min_limit;
reg [15:0] cfg_velocity_max_limit;
reg [15:0] cfg_actuator_min_limit;
reg [15:0] cfg_actuator_max_limit;
reg [15:0] cfg_actuator_safe_position;
reg [15:0] cfg_command_timeout_cycles;
reg [15:0] cfg_max_slew_rate;
reg [7:0] cfg_geometry_format_id;
reg [7:0] cfg_geometry_source_id;
reg [15:0] cfg_geometry_version;
reg cfg_clear_faults;
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        cfg_enable <= 1'b0;
        cfg_stream_velocity_mps_setpoint <= 16'd20;
        cfg_velocity_min_limit <= 16'd20;
        cfg_velocity_max_limit <= 16'd55;
        cfg_actuator_min_limit <= 16'd0;
        cfg_actuator_max_limit <= 16'd255;
        cfg_actuator_safe_position <= 16'd0;
        cfg_command_timeout_cycles <= 16'd1000;
        cfg_max_slew_rate <= 16'd0;
        cfg_geometry_format_id <= 8'd0;
        cfg_geometry_source_id <= 8'd0;
        cfg_geometry_version <= 16'd0;
        cfg_clear_faults <= 1'b0;
        host_reg_rvalid <= 1'b0;
        host_reg_rdata <= 32'd0;
        host_reg_ready <= 1'b1;
    end else begin
        host_reg_ready <= 1'b1;
        host_reg_rvalid <= host_reg_rd_valid & host_reg_ready;
        cfg_clear_faults <= 1'b0;
        if (host_reg_wr_valid & host_reg_ready) begin
            case (host_reg_addr)
                8'h00: begin
                    cfg_enable <= host_reg_wdata[0];
                    cfg_clear_faults <= host_reg_wdata[1];
                end
                8'h01: cfg_stream_velocity_mps_setpoint[7:0] <= host_reg_wdata[7:0];
                8'h02: cfg_stream_velocity_mps_setpoint[15:8] <= host_reg_wdata[7:0];
                8'h03: cfg_velocity_min_limit[7:0] <= host_reg_wdata[7:0];
                8'h04: cfg_velocity_min_limit[15:8] <= host_reg_wdata[7:0];
                8'h05: cfg_velocity_max_limit[7:0] <= host_reg_wdata[7:0];
                8'h06: cfg_velocity_max_limit[15:8] <= host_reg_wdata[7:0];
                8'h07: cfg_actuator_min_limit[7:0] <= host_reg_wdata[7:0];
                8'h08: cfg_actuator_min_limit[15:8] <= host_reg_wdata[7:0];
                8'h09: cfg_actuator_max_limit[7:0] <= host_reg_wdata[7:0];
                8'h0A: cfg_actuator_max_limit[15:8] <= host_reg_wdata[7:0];
                8'h0B: cfg_actuator_safe_position[7:0] <= host_reg_wdata[7:0];
                8'h0C: cfg_actuator_safe_position[15:8] <= host_reg_wdata[7:0];
                8'h0D: cfg_command_timeout_cycles[7:0] <= host_reg_wdata[7:0];
                8'h0E: cfg_command_timeout_cycles[15:8] <= host_reg_wdata[7:0];
                8'h0F: cfg_max_slew_rate[7:0] <= host_reg_wdata[7:0];
                8'h10: cfg_max_slew_rate[15:8] <= host_reg_wdata[7:0];
                8'h11: cfg_geometry_format_id <= host_reg_wdata[7:0];
                8'h12: cfg_geometry_source_id <= host_reg_wdata[7:0];
                8'h13: cfg_geometry_version[7:0] <= host_reg_wdata[7:0];
                8'h14: cfg_geometry_version[15:8] <= host_reg_wdata[7:0];
                default: begin end
            endcase
        end
        if (host_reg_rd_valid & host_reg_ready) begin
            case (host_reg_addr)
                8'h00: host_reg_rdata <= {24'd0, cfg_clear_faults, cfg_enable};
                8'h01: host_reg_rdata <= {24'd0, cfg_stream_velocity_mps_setpoint[7:0]};
                8'h02: host_reg_rdata <= {24'd0, cfg_stream_velocity_mps_setpoint[15:8]};
                8'h03: host_reg_rdata <= {24'd0, cfg_velocity_min_limit[7:0]};
                8'h04: host_reg_rdata <= {24'd0, cfg_velocity_min_limit[15:8]};
                8'h05: host_reg_rdata <= {24'd0, cfg_velocity_max_limit[7:0]};
                8'h06: host_reg_rdata <= {24'd0, cfg_velocity_max_limit[15:8]};
                8'h07: host_reg_rdata <= {24'd0, cfg_actuator_min_limit[7:0]};
                8'h08: host_reg_rdata <= {24'd0, cfg_actuator_min_limit[15:8]};
                8'h09: host_reg_rdata <= {24'd0, cfg_actuator_max_limit[7:0]};
                8'h0A: host_reg_rdata <= {24'd0, cfg_actuator_max_limit[15:8]};
                8'h0B: host_reg_rdata <= {24'd0, cfg_actuator_safe_position[7:0]};
                8'h0C: host_reg_rdata <= {24'd0, cfg_actuator_safe_position[15:8]};
                8'h0D: host_reg_rdata <= {24'd0, cfg_command_timeout_cycles[7:0]};
                8'h0E: host_reg_rdata <= {24'd0, cfg_command_timeout_cycles[15:8]};
                8'h0F: host_reg_rdata <= {24'd0, cfg_max_slew_rate[7:0]};
                8'h10: host_reg_rdata <= {24'd0, cfg_max_slew_rate[15:8]};
                8'h11: host_reg_rdata <= {24'd0, cfg_geometry_format_id};
                8'h12: host_reg_rdata <= {24'd0, cfg_geometry_source_id};
                8'h13: host_reg_rdata <= {24'd0, cfg_geometry_version[7:0]};
                8'h14: host_reg_rdata <= {24'd0, cfg_geometry_version[15:8]};
                8'h20: host_reg_rdata <= {24'd0, status_last_fault_code, status_current_state};
                8'h21: host_reg_rdata <= {24'd0, status_stale_reject_count[7:0]};
                8'h22: host_reg_rdata <= {24'd0, status_stale_reject_count[15:8]};
                8'h23: host_reg_rdata <= {24'd0, status_clamp_event_count[7:0]};
                8'h24: host_reg_rdata <= {24'd0, status_clamp_event_count[15:8]};
                8'h25: host_reg_rdata <= {24'd0, 4'd0, status_model_response_valid_seen, status_request_inflight, status_fallback_active};
                8'h26: host_reg_rdata <= {24'd0, status_last_accepted_seq[7:0]};
                8'h27: host_reg_rdata <= {24'd0, status_last_accepted_seq[15:8]};
                8'h28: host_reg_rdata <= {24'd0, status_last_response_age[7:0]};
                8'h29: host_reg_rdata <= {24'd0, status_last_response_age[15:8]};
                8'h2A: host_reg_rdata <= {24'd0, 8'd0};
                8'h2B: host_reg_rdata <= {24'd0, 8'd0};
                8'h2C: host_reg_rdata <= {24'd0, 8'd0};
                8'h2D: host_reg_rdata <= {24'd0, 8'd0};
                8'h30: host_reg_rdata <= {24'd0, cfg_geometry_version[7:0]};
                8'h31: host_reg_rdata <= {24'd0, cfg_geometry_version[15:8]};
                default: host_reg_rdata <= 32'd0;
            endcase
        end
    end
end
endmodule
