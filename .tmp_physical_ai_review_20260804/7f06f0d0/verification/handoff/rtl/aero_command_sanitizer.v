module aero_command_sanitizer(
    clk,
    rst_n,
    cfg_actuator_min_limit,
    cfg_actuator_max_limit,
    cfg_actuator_safe_position,
    cfg_max_slew_rate,
    cfg_enable,
    fallback_active_in,
    fault_active_in,
    req_seq,
    rsp_valid,
    rsp_seq,
    rsp_drag_force,
    rsp_lift_force,
    rsp_surface_pressure,
    rsp_flow_field,
    safe_position_source,
    cmd_position,
    cmd_valid,
    cmd_enable,
    cmd_seq,
    fallback_active_out,
    clamp_applied,
    clamp_event_pulse,
    sanitized_position
);
input clk;
input rst_n;
input [15:0] cfg_actuator_min_limit;
input [15:0] cfg_actuator_max_limit;
input [15:0] cfg_actuator_safe_position;
input [15:0] cfg_max_slew_rate;
input cfg_enable;
input fallback_active_in;
input fault_active_in;
input [15:0] req_seq;
input rsp_valid;
input [15:0] rsp_seq;
input [15:0] rsp_drag_force;
input [15:0] rsp_lift_force;
input [15:0] rsp_surface_pressure;
input [15:0] rsp_flow_field;
input [15:0] safe_position_source;
output [15:0] cmd_position;
output cmd_valid;
output cmd_enable;
output [15:0] cmd_seq;
output fallback_active_out;
output clamp_applied;
output clamp_event_pulse;
output [15:0] sanitized_position;
reg [15:0] cmd_position;
reg cmd_valid;
reg cmd_enable;
reg [15:0] cmd_seq;
reg fallback_active_out;
reg clamp_applied;
reg clamp_event_pulse;
reg [15:0] sanitized_position;
reg [15:0] prev_cmd_position;
reg [15:0] raw_cmd_position;
reg [15:0] clamped_position;
reg [15:0] slewed_position;
reg clamp_now;
reg valid_path;
always @(*) begin
    raw_cmd_position = rsp_drag_force + rsp_lift_force + rsp_surface_pressure + rsp_flow_field;
    valid_path = cfg_enable & rsp_valid & (rsp_seq == req_seq) & ~fallback_active_in & ~fault_active_in;
    clamp_now = 1'b0;
    clamped_position = raw_cmd_position;
    slewed_position = clamped_position;
    if (valid_path) begin
        if (raw_cmd_position < cfg_actuator_min_limit) begin
            clamped_position = cfg_actuator_min_limit;
            clamp_now = 1'b1;
        end else if (raw_cmd_position > cfg_actuator_max_limit) begin
            clamped_position = cfg_actuator_max_limit;
            clamp_now = 1'b1;
        end
        if (cfg_max_slew_rate != 16'd0) begin
            if (clamped_position > (prev_cmd_position + cfg_max_slew_rate)) begin
                slewed_position = prev_cmd_position + cfg_max_slew_rate;
                clamp_now = 1'b1;
            end else if (clamped_position < (prev_cmd_position - cfg_max_slew_rate)) begin
                slewed_position = prev_cmd_position - cfg_max_slew_rate;
                clamp_now = 1'b1;
            end else begin
                slewed_position = clamped_position;
            end
        end else begin
            slewed_position = clamped_position;
        end
    end else begin
        clamped_position = cfg_actuator_safe_position;
        slewed_position = safe_position_source;
        clamp_now = 1'b0;
    end
end
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        cmd_position <= 16'd0;
        cmd_valid <= 1'b0;
        cmd_enable <= 1'b0;
        cmd_seq <= 16'd0;
        fallback_active_out <= 1'b1;
        clamp_applied <= 1'b0;
        clamp_event_pulse <= 1'b0;
        sanitized_position <= 16'd0;
        prev_cmd_position <= 16'd0;
    end else begin
        fallback_active_out <= fallback_active_in | fault_active_in;
        clamp_applied <= clamp_now;
        clamp_event_pulse <= clamp_now;
        if (fallback_active_in | fault_active_in) begin
            cmd_position <= safe_position_source;
            sanitized_position <= safe_position_source;
            cmd_valid <= 1'b1;
            cmd_enable <= 1'b0;
            cmd_seq <= req_seq;
            prev_cmd_position <= safe_position_source;
        end else begin
            cmd_position <= slewed_position;
            sanitized_position <= slewed_position;
            cmd_valid <= rsp_valid & (rsp_seq == req_seq) & cfg_enable;
            cmd_enable <= rsp_valid & (rsp_seq == req_seq) & cfg_enable;
            cmd_seq <= req_seq;
            prev_cmd_position <= slewed_position;
        end
    end
end
endmodule
