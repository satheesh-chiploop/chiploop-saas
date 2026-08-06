module geometry_ingress (
    clk,
    reset_n,
    vehicle_geometry_valid,
    geometry_format,
    geometry_source,
    geometry_metadata,
    geometry_valid,
    geometry_reject,
    geometry_descriptor
);
input clk;
input reset_n;
input vehicle_geometry_valid;
input [2:0] geometry_format;
input [3:0] geometry_source;
input [63:0] geometry_metadata;
output geometry_valid;
output geometry_reject;
output [127:0] geometry_descriptor;
reg geometry_valid_r;
reg geometry_reject_r;
reg [127:0] geometry_descriptor_r;
reg [127:0] geometry_descriptor_next;

wire format_ok;
wire metadata_ok;
wire accept_pulse;
wire reject_pulse;

assign format_ok = (geometry_format == 3'b001);
assign metadata_ok = |geometry_metadata;
assign accept_pulse = vehicle_geometry_valid & format_ok & metadata_ok;
assign reject_pulse = vehicle_geometry_valid & ~(format_ok & metadata_ok);

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        geometry_valid_r <= 1'b0;
        geometry_reject_r <= 1'b0;
        geometry_descriptor_r <= 128'h00000000000000000000000000000000;
    end else begin
        geometry_valid_r <= accept_pulse;
        geometry_reject_r <= reject_pulse;
        if (accept_pulse) begin
            geometry_descriptor_r <= {geometry_source, geometry_format, geometry_metadata, 48'h000000000000};
        end
    end
end

always @(*) begin
    geometry_descriptor_next = geometry_descriptor_r;
    if (accept_pulse) begin
        geometry_descriptor_next = {geometry_source, geometry_format, geometry_metadata, 48'h000000000000};
    end
end

assign geometry_valid = geometry_valid_r;
assign geometry_reject = geometry_reject_r;
assign geometry_descriptor = geometry_descriptor_r;

endmodule
