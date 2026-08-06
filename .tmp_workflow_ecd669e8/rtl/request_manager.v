module request_manager (
    input         clk,
    input         rst_n,
    input         control_valid,
    input         vehicle_geometry_valid,
    input         flow_conditions_valid,
    input  [31:0] stream_velocity_mps,
    input  [127:0] geometry_ref,
    input         host_fallback_route_en,
    input  [31:0] host_operating_en_min_mps,
    input  [31:0] host_operating_en_max_mps,
    input         request_launch_grant,
    input         outstanding_clear,
    output [15:0] request_id_out,
    output [15:0] request_seq_out,
    output [31:0] request_timestamp_out,
    output [255:0] request_payload_out,
    input         request_valid_out,
    output        request_pending_out,
    output        envelope_violation_out
);
    reg [15:0] request_id_r;
    reg [15:0] request_seq_r;
    reg [31:0] request_timestamp_r;
    reg [255:0] request_payload_r;
    reg        request_pending_r;
    reg        envelope_violation_r;
    reg [31:0] cycle_ctr;
    wire       within_envelope;
    wire       qualified;
    wire       launch;

    assign within_envelope = ((stream_velocity_mps >= host_operating_en_min_mps) && (stream_velocity_mps <= host_operating_en_max_mps)) || host_fallback_route_en;
    assign qualified = control_valid & vehicle_geometry_valid & flow_conditions_valid & within_envelope;
    assign launch = qualified & request_launch_grant & ~request_pending_r;

    assign request_id_out = request_id_r;
    assign request_seq_out = request_seq_r;
    assign request_timestamp_out = request_timestamp_r;
    assign request_payload_out = request_payload_r;
    assign request_pending_out = request_pending_r;
    assign envelope_violation_out = envelope_violation_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            request_id_r <= 16'h0000;
            request_seq_r <= 16'h0000;
            request_timestamp_r <= 32'h0000_0000;
            request_payload_r <= 256'h0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000;
            request_pending_r <= 1'b0;
            envelope_violation_r <= 1'b0;
            cycle_ctr <= 32'h0000_0000;
        end else begin
            cycle_ctr <= cycle_ctr + 32'h0000_0001;
            envelope_violation_r <= qualified & ~within_envelope;
            if (outstanding_clear) begin
                request_pending_r <= 1'b0;
            end
            if (launch) begin
                request_id_r <= request_id_r + 16'h0001;
                request_seq_r <= request_seq_r + 16'h0001;
                request_timestamp_r <= cycle_ctr;
                request_payload_r <= {16'h0000, request_id_r + 16'h0001, request_seq_r + 16'h0001, cycle_ctr, geometry_ref, stream_velocity_mps, host_fallback_route_en, host_operating_en_min_mps, host_operating_en_max_mps, 31'h0};
                request_pending_r <= 1'b1;
            end
        end
    end
endmodule
