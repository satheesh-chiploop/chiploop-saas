module domino_input_supervisor (
    clk,
    rst_n,
    cfg_stream_velocity_low_limit,
    cfg_stream_velocity_high_limit,
    cfg_geometry_format_selector,
    stream_velocity_mps,
    flow_update_strobe,
    geometry_update_strobe,
    geometry_format_selector,
    geometry_metadata_valid,
    geometry_metadata_tag,
    geometry_handle_in,
    geometry_reference_is_driaverml_stl,
    flow_epoch,
    geometry_epoch,
    active_epoch,
    validated_stream_velocity_mps,
    geometry_handle_canonical,
    geometry_valid,
    flow_valid,
    geometry_fault,
    flow_fault,
    envelope_in_range,
    input_update_strobe
);
input clk;
input rst_n;
input [15:0] cfg_stream_velocity_low_limit;
input [15:0] cfg_stream_velocity_high_limit;
input [7:0] cfg_geometry_format_selector;
input [15:0] stream_velocity_mps;
input flow_update_strobe;
input geometry_update_strobe;
input [7:0] geometry_format_selector;
input geometry_metadata_valid;
input [15:0] geometry_metadata_tag;
input [31:0] geometry_handle_in;
input geometry_reference_is_driaverml_stl;
output reg [31:0] flow_epoch;
output reg [31:0] geometry_epoch;
output reg [31:0] active_epoch;
output reg [15:0] validated_stream_velocity_mps;
output reg [31:0] geometry_handle_canonical;
output reg geometry_valid;
output reg flow_valid;
output reg geometry_fault;
output reg flow_fault;
output reg envelope_in_range;
output reg input_update_strobe;

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        flow_epoch <= 32'h00000000;
        geometry_epoch <= 32'h00000000;
        active_epoch <= 32'h00000000;
        validated_stream_velocity_mps <= 16'h0000;
        geometry_handle_canonical <= 32'h00000000;
        geometry_valid <= 1'b0;
        flow_valid <= 1'b0;
        geometry_fault <= 1'b0;
        flow_fault <= 1'b0;
        envelope_in_range <= 1'b0;
        input_update_strobe <= 1'b0;
    end else begin
        input_update_strobe <= flow_update_strobe | geometry_update_strobe;
        if (flow_update_strobe) begin
            validated_stream_velocity_mps <= stream_velocity_mps;
            flow_epoch <= flow_epoch + 32'h00000001;
            flow_valid <= (stream_velocity_mps >= cfg_stream_velocity_low_limit) & (stream_velocity_mps <= cfg_stream_velocity_high_limit);
            envelope_in_range <= (stream_velocity_mps >= cfg_stream_velocity_low_limit) & (stream_velocity_mps <= cfg_stream_velocity_high_limit);
            flow_fault <= ~((stream_velocity_mps >= cfg_stream_velocity_low_limit) & (stream_velocity_mps <= cfg_stream_velocity_high_limit));
        end
        if (geometry_update_strobe) begin
            geometry_epoch <= geometry_epoch + 32'h00000001;
            geometry_handle_canonical <= geometry_handle_in;
            geometry_valid <= geometry_metadata_valid & (geometry_format_selector == cfg_geometry_format_selector) & geometry_reference_is_driaverml_stl;
            geometry_fault <= ~(geometry_metadata_valid & (geometry_format_selector == cfg_geometry_format_selector) & geometry_reference_is_driaverml_stl);
        end
        active_epoch <= flow_epoch ^ geometry_epoch;
        if (!geometry_metadata_valid) begin
            geometry_fault <= 1'b1;
        end
        if (~((stream_velocity_mps >= cfg_stream_velocity_low_limit) & (stream_velocity_mps <= cfg_stream_velocity_high_limit))) begin
            flow_fault <= 1'b1;
        end
    end
end
endmodule
