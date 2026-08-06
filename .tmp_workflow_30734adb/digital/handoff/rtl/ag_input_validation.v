module ag_input_validation(
    clk,
    rst_n,
    i_vehicle_geometry,
    i_flow_conditions,
    i_cfg,
    geometry_valid,
    geometry_error,
    flow_valid,
    out_of_envelope,
    configuration_valid,
    geometry_revision,
    sanitized_geometry,
    sanitized_flow,
    reference_operating_tag,
    config_fault
);
input clk;
input rst_n;
input [255:0] i_vehicle_geometry;
input [95:0] i_flow_conditions;
input [255:0] i_cfg;
output geometry_valid;
output geometry_error;
output flow_valid;
output out_of_envelope;
output configuration_valid;
output [15:0] geometry_revision;
output [127:0] sanitized_geometry;
output [95:0] sanitized_flow;
output [15:0] reference_operating_tag;
output config_fault;

reg geometry_valid_r;
reg geometry_error_r;
reg flow_valid_r;
reg out_of_envelope_r;
reg configuration_valid_r;
reg [15:0] geometry_revision_r;
reg [127:0] sanitized_geometry_r;
reg [95:0] sanitized_flow_r;
reg [15:0] reference_operating_tag_r;
reg config_fault_r;

wire geom_accept;
wire geom_source_present;
wire geom_format_stl;
wire geom_format_approved;
wire [15:0] flow_vel;
wire flow_low_ok;
wire flow_high_ok;
wire [15:0] cfg_envelope_min;
wire [15:0] cfg_envelope_max;

assign cfg_envelope_min = {8'b0, i_cfg[47:40]};
assign cfg_envelope_max = {8'b0, i_cfg[63:56]};
assign geom_format_stl = i_vehicle_geometry[0];
assign geom_format_approved = i_cfg[8];
assign geom_source_present = i_vehicle_geometry[1];
assign geom_accept = (geom_format_stl & i_cfg[0]) | (geom_format_approved & i_cfg[1]);
assign flow_vel = i_flow_conditions[15:0];
assign flow_low_ok = (flow_vel >= cfg_envelope_min);
assign flow_high_ok = (flow_vel <= cfg_envelope_max);

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        geometry_valid_r <= 1'b0;
        geometry_error_r <= 1'b0;
        flow_valid_r <= 1'b0;
        out_of_envelope_r <= 1'b0;
        configuration_valid_r <= 1'b0;
        geometry_revision_r <= 16'h0000;
        sanitized_geometry_r <= 128'h00000000000000000000000000000000;
        sanitized_flow_r <= 96'h000000000000000000000000;
        reference_operating_tag_r <= 16'h0000;
        config_fault_r <= 1'b0;
    end else begin
        geometry_valid_r <= geom_accept & geom_source_present & i_cfg[2];
        geometry_error_r <= (~geom_accept) | (~geom_source_present);
        out_of_envelope_r <= (~flow_low_ok) | (~flow_high_ok);
        flow_valid_r <= flow_low_ok & flow_high_ok;
        configuration_valid_r <= i_cfg[4] & ~i_cfg[7] & ~i_cfg[9];
        geometry_revision_r <= i_vehicle_geometry[31:16];
        sanitized_geometry_r <= i_vehicle_geometry[159:32];
        sanitized_flow_r <= i_flow_conditions;
        reference_operating_tag_r <= 16'h2691;
        config_fault_r <= ~i_cfg[4];
    end
end

assign geometry_valid = geometry_valid_r;
assign geometry_error = geometry_error_r;
assign flow_valid = flow_valid_r;
assign out_of_envelope = out_of_envelope_r;
assign configuration_valid = configuration_valid_r;
assign geometry_revision = geometry_revision_r;
assign sanitized_geometry = sanitized_geometry_r;
assign sanitized_flow = sanitized_flow_r;
assign reference_operating_tag = reference_operating_tag_r;
assign config_fault = config_fault_r;

endmodule
