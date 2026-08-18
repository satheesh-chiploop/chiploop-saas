module adaptive_aero_control_top_actuator_safety (
    clk,
    reset_n,
    cfg_clamp_min,
    cfg_clamp_max,
    cfg_rate_limit_en,
    cfg_rate_limit_step,
    cfg_fallback_cmd,
    reg_fallback_active,
    reg_envelope_violation,
    reg_timeout_expired,
    reg_stale_reject,
    reg_service_error,
    reg_pending,
    selected_cmd_o,
    selected_cmd_valid_o,
    last_accepted_cmd_o,
    actuator_cmd_o,
    actuator_cmd_valid_o,
    reg_clamp_active,
    reg_last_accepted_cmd
);

input clk;
input reset_n;
input [15:0] cfg_clamp_min;
input [15:0] cfg_clamp_max;
input cfg_rate_limit_en;
input [15:0] cfg_rate_limit_step;
input [15:0] cfg_fallback_cmd;
input reg_fallback_active;
input reg_envelope_violation;
input reg_timeout_expired;
input reg_stale_reject;
input reg_service_error;
input reg_pending;
input [15:0] selected_cmd_o;
input selected_cmd_valid_o;
output [15:0] last_accepted_cmd_o;
output [15:0] actuator_cmd_o;
output actuator_cmd_valid_o;
output reg_clamp_active;
output [15:0] reg_last_accepted_cmd;
reg [15:0] last_accepted_cmd_r;
reg [15:0] actuator_cmd_r;
reg actuator_cmd_valid_r;
reg reg_clamp_active_r;

wire fault_mode;
wire [15:0] clamp_min_eff;
wire [15:0] clamp_max_eff;
wire [15:0] rate_step_eff;
wire [15:0] pre_clamped_cmd;
wire [15:0] rate_limited_cmd;
wire [15:0] bounded_cmd;
wire clamp_low;
wire clamp_high;
wire step_up;
wire step_down;
wire [15:0] delta_up;
wire [15:0] delta_down;

assign fault_mode = reg_fallback_active | reg_envelope_violation | reg_timeout_expired | reg_stale_reject | reg_service_error;
assign clamp_min_eff = cfg_clamp_min;
assign clamp_max_eff = cfg_clamp_max;
assign rate_step_eff = (cfg_rate_limit_step == 16'h0000) ? 16'h0001 : cfg_rate_limit_step;

assign delta_up = selected_cmd_o - last_accepted_cmd_r;
assign delta_down = last_accepted_cmd_r - selected_cmd_o;
assign step_up = (selected_cmd_o > last_accepted_cmd_r) && (delta_up > rate_step_eff);
assign step_down = (selected_cmd_o < last_accepted_cmd_r) && (delta_down > rate_step_eff);

assign pre_clamped_cmd = (selected_cmd_o < clamp_min_eff) ? clamp_min_eff : selected_cmd_o;
assign bounded_cmd = (pre_clamped_cmd > clamp_max_eff) ? clamp_max_eff : pre_clamped_cmd;
assign rate_limited_cmd = step_up ? (last_accepted_cmd_r + rate_step_eff) :
                          step_down ? (last_accepted_cmd_r - rate_step_eff) :
                          bounded_cmd;
assign clamp_low = (selected_cmd_o < clamp_min_eff);
assign clamp_high = (selected_cmd_o > clamp_max_eff);

assign last_accepted_cmd_o = last_accepted_cmd_r;
assign actuator_cmd_o = actuator_cmd_r;
assign actuator_cmd_valid_o = actuator_cmd_valid_r;
assign reg_clamp_active = reg_clamp_active_r;
assign reg_last_accepted_cmd = last_accepted_cmd_r;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        last_accepted_cmd_r <= 16'h0000;
        actuator_cmd_r <= 16'h0000;
        actuator_cmd_valid_r <= 1'b0;
        reg_clamp_active_r <= 1'b0;
    end else begin
        reg_clamp_active_r <= 1'b0;
        actuator_cmd_valid_r <= 1'b0;
        if (fault_mode || !selected_cmd_valid_o || !reg_pending) begin
            actuator_cmd_r <= cfg_fallback_cmd;
            actuator_cmd_valid_r <= selected_cmd_valid_o;
            if (cfg_fallback_cmd != last_accepted_cmd_r) begin
                reg_clamp_active_r <= 1'b1;
            end
            if (reg_fallback_active || reg_envelope_violation || reg_timeout_expired || reg_stale_reject || reg_service_error) begin
                last_accepted_cmd_r <= cfg_fallback_cmd;
            end
        end else begin
            if (cfg_rate_limit_en) begin
                actuator_cmd_r <= rate_limited_cmd;
                if ((rate_limited_cmd != selected_cmd_o) || clamp_low || clamp_high || step_up || step_down) begin
                    reg_clamp_active_r <= 1'b1;
                end
            end else begin
                actuator_cmd_r <= bounded_cmd;
                if (clamp_low || clamp_high) begin
                    reg_clamp_active_r <= 1'b1;
                end
            end
            actuator_cmd_valid_r <= 1'b1;
            last_accepted_cmd_r <= actuator_cmd_r;
        end
    end
end

endmodule
