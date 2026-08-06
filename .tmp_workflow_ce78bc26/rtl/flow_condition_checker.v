module flow_condition_checker (
    clk,
    reset_n,
    stream_velocity_mps,
    flow_metadata,
    flow_valid,
    envelope_fault,
    nominal_condition,
    flow_descriptor
);
input clk;
input reset_n;
input [15:0] stream_velocity_mps;
input [31:0] flow_metadata;
output flow_valid;
output envelope_fault;
output nominal_condition;
output [63:0] flow_descriptor;
reg flow_valid_r;
reg envelope_fault_r;
reg nominal_condition_r;
reg [63:0] flow_descriptor_r;
wire in_range;
wire nominal_match;

assign in_range = (stream_velocity_mps >= 16'd20) && (stream_velocity_mps <= 16'd55);
assign nominal_match = (stream_velocity_mps == 16'd3890);

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        flow_valid_r <= 1'b0;
        envelope_fault_r <= 1'b0;
        nominal_condition_r <= 1'b0;
        flow_descriptor_r <= 64'h0000000000000000;
    end else begin
        flow_valid_r <= in_range;
        envelope_fault_r <= ~in_range;
        nominal_condition_r <= nominal_match;
        flow_descriptor_r <= {flow_metadata, stream_velocity_mps, 16'h0000};
    end
end

assign flow_valid = flow_valid_r;
assign envelope_fault = envelope_fault_r;
assign nominal_condition = nominal_condition_r;
assign flow_descriptor = flow_descriptor_r;

endmodule
