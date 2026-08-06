module ag_command_and_safety_fsm(
    clk,
    rst_n,
    geometry_valid,
    flow_valid,
    configuration_valid,
    geometry_error,
    out_of_envelope,
    response_error,
    stale_detected,
    model_data_valid,
    drag_force,
    lift_force,
    surface_pressure,
    flow_field_meta,
    request_id_in,
    actuator_feedback,
    cfg,
    o_actuator_command,
    o_safety_state,
    o_telemetry,
    fallback_active,
    clamp_applied,
    actuator_fault,
    current_state,
    last_valid_command,
    safety_inhibit
);
input clk;
input rst_n;
input geometry_valid;
input flow_valid;
input configuration_valid;
input geometry_error;
input out_of_envelope;
input response_error;
input stale_detected;
input model_data_valid;
input [31:0] drag_force;
input [31:0] lift_force;
input [31:0] surface_pressure;
input [63:0] flow_field_meta;
input [15:0] request_id_in;
input [31:0] actuator_feedback;
input [255:0] cfg;
output [31:0] o_actuator_command;
output [63:0] o_safety_state;
output [255:0] o_telemetry;
output fallback_active;
output clamp_applied;
output actuator_fault;
output [7:0] current_state;
output [31:0] last_valid_command;
output safety_inhibit;

localparam [7:0] RESET_SAFE = 8'h00;
localparam [7:0] IDLE_SAFE = 8'h01;
localparam [7:0] REQUEST_PENDING = 8'h02;
localparam [7:0] VALIDATING_RESPONSE = 8'h03;
localparam [7:0] COMMAND_ACTIVE = 8'h04;
localparam [7:0] CLAMPED_ACTIVE = 8'h05;
localparam [7:0] FALLBACK_ACTIVE = 8'h06;
localparam [7:0] FAULT_LOCK = 8'h07;

reg [7:0] state_r;
reg [31:0] actuator_command_r;
reg [63:0] safety_state_r;
reg [255:0] telemetry_r;
reg fallback_active_r;
reg clamp_applied_r;
reg actuator_fault_r;
reg [31:0] last_valid_command_r;
reg safety_inhibit_r;

wire safety_fault;
wire [31:0] modeled_command;
wire [31:0] clamped_command;
wire clamp_hi;
wire clamp_lo;
wire [31:0] cmd_min;
wire [31:0] cmd_max;

assign cmd_min = cfg[127:96];
assign cmd_max = cfg[159:128];
assign modeled_command = drag_force ^ lift_force ^ surface_pressure ^ {24'b0, flow_field_meta[7:0]};
assign clamp_hi = (modeled_command > cmd_max);
assign clamp_lo = (modeled_command < cmd_min);
assign clamped_command = clamp_hi ? cmd_max : (clamp_lo ? cmd_min : modeled_command);
assign safety_fault = geometry_error | out_of_envelope | response_error | stale_detected | actuator_fault_r | ~configuration_valid | ~geometry_valid | ~flow_valid;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state_r <= RESET_SAFE;
        actuator_command_r <= 32'h00000000;
        safety_state_r <= 64'h0000000000000000;
        telemetry_r <= 256'h0000000000000000000000000000000000000000000000000000000000000000;
        fallback_active_r <= 1'b1;
        clamp_applied_r <= 1'b0;
        actuator_fault_r <= 1'b0;
        last_valid_command_r <= 32'h00000000;
        safety_inhibit_r <= 1'b1;
    end else begin
        case (state_r)
            RESET_SAFE: begin
                state_r <= IDLE_SAFE;
                fallback_active_r <= 1'b1;
                safety_inhibit_r <= 1'b1;
                actuator_command_r <= 32'h00000000;
            end
            IDLE_SAFE: begin
                safety_inhibit_r <= ~configuration_valid;
                if (geometry_valid & flow_valid & configuration_valid) state_r <= REQUEST_PENDING;
                if (safety_fault) state_r <= FALLBACK_ACTIVE;
            end
            REQUEST_PENDING: begin
                if (model_data_valid) state_r <= VALIDATING_RESPONSE;
                if (safety_fault) state_r <= FALLBACK_ACTIVE;
            end
            VALIDATING_RESPONSE: begin
                if (model_data_valid & ~safety_fault) begin
                    state_r <= (clamp_hi | clamp_lo) ? CLAMPED_ACTIVE : COMMAND_ACTIVE;
                    actuator_command_r <= clamped_command;
                    last_valid_command_r <= clamped_command;
                    clamp_applied_r <= clamp_hi | clamp_lo;
                    fallback_active_r <= 1'b0;
                end else if (safety_fault) begin
                    state_r <= FALLBACK_ACTIVE;
                end
            end
            COMMAND_ACTIVE: begin
                actuator_command_r <= clamped_command;
                last_valid_command_r <= clamped_command;
                clamp_applied_r <= clamp_hi | clamp_lo;
                fallback_active_r <= 1'b0;
                if (clamp_hi | clamp_lo) state_r <= CLAMPED_ACTIVE;
                if (safety_fault) state_r <= FALLBACK_ACTIVE;
            end
            CLAMPED_ACTIVE: begin
                actuator_command_r <= clamped_command;
                last_valid_command_r <= clamped_command;
                clamp_applied_r <= 1'b1;
                fallback_active_r <= 1'b0;
                if (~(clamp_hi | clamp_lo)) state_r <= COMMAND_ACTIVE;
                if (safety_fault) state_r <= FALLBACK_ACTIVE;
            end
            FALLBACK_ACTIVE: begin
                fallback_active_r <= 1'b1;
                safety_inhibit_r <= 1'b1;
                actuator_command_r <= cfg[55:24];
                if (cfg[2] & cfg[0]) state_r <= FAULT_LOCK;
            end
            FAULT_LOCK: begin
                fallback_active_r <= 1'b1;
                safety_inhibit_r <= 1'b1;
                actuator_command_r <= cfg[55:24];
                if (cfg[2] & cfg[0]) state_r <= IDLE_SAFE;
            end
            default: begin
                state_r <= RESET_SAFE;
            end
        endcase
        actuator_fault_r <= actuator_fault_r | actuator_feedback[0] | actuator_feedback[1];
        safety_state_r <= {56'b0, state_r};
        telemetry_r <= {cfg[63:0], cfg[127:64], cfg[191:128], cfg[255:192]};
    end
end

assign o_actuator_command = actuator_command_r;
assign o_safety_state = safety_state_r;
assign o_telemetry = telemetry_r;
assign fallback_active = fallback_active_r;
assign clamp_applied = clamp_applied_r;
assign actuator_fault = actuator_fault_r;
assign current_state = state_r;
assign last_valid_command = last_valid_command_r;
assign safety_inhibit = safety_inhibit_r;

endmodule
