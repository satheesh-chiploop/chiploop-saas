module response_validator (
    input         clk,
    input         rst_n,
    input         model_response_valid,
    input  [255:0] model_response_payload,
    input  [15:0] outstanding_request_id,
    input  [15:0] outstanding_request_seq,
    input  [31:0] outstanding_timestamp,
    input  [31:0] freshness_window_cycles,
    output        response_accepted_out,
    output        response_stale_out,
    output        response_invalid_out,
    output        response_timeout_out,
    output [31:0] drag_force_out,
    output [31:0] lift_force_out,
    output [31:0] surface_pressure_out,
    output [63:0] flow_field_meta_out,
    output        response_payload_valid_out
);
    reg response_accepted_r;
    reg response_stale_r;
    reg response_invalid_r;
    reg response_timeout_r;
    reg [31:0] drag_force_r;
    reg [31:0] lift_force_r;
    reg [31:0] surface_pressure_r;
    reg [63:0] flow_field_meta_r;
    reg response_payload_valid_r;
    wire id_match;
    wire seq_match;
    wire format_ok;
    wire age_ok;
    wire accepted;
    wire [31:0] response_age;

    assign id_match = (model_response_payload[255:240] == outstanding_request_id);
    assign seq_match = (model_response_payload[239:224] == outstanding_request_seq);
    assign response_age = 32'h0000_0000;
    assign format_ok = 1'b1;
    assign age_ok = (freshness_window_cycles != 32'h0000_0000) ? (response_age <= freshness_window_cycles) : 1'b1;
    assign accepted = model_response_valid & id_match & seq_match & format_ok & age_ok;

    assign response_accepted_out = response_accepted_r;
    assign response_stale_out = response_stale_r;
    assign response_invalid_out = response_invalid_r;
    assign response_timeout_out = response_timeout_r;
    assign drag_force_out = drag_force_r;
    assign lift_force_out = lift_force_r;
    assign surface_pressure_out = surface_pressure_r;
    assign flow_field_meta_out = flow_field_meta_r;
    assign response_payload_valid_out = response_payload_valid_r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            response_accepted_r <= 1'b0;
            response_stale_r <= 1'b0;
            response_invalid_r <= 1'b0;
            response_timeout_r <= 1'b0;
            drag_force_r <= 32'h0000_0000;
            lift_force_r <= 32'h0000_0000;
            surface_pressure_r <= 32'h0000_0000;
            flow_field_meta_r <= 64'h0000_0000_0000_0000;
            response_payload_valid_r <= 1'b0;
        end else begin
            response_accepted_r <= accepted;
            response_stale_r <= model_response_valid & ~(id_match & seq_match);
            response_invalid_r <= model_response_valid & ~(format_ok);
            response_timeout_r <= model_response_valid & ~age_ok;
            response_payload_valid_r <= accepted;
            if (accepted) begin
                drag_force_r <= model_response_payload[31:0];
                lift_force_r <= model_response_payload[63:32];
                surface_pressure_r <= model_response_payload[95:64];
                flow_field_meta_r <= model_response_payload[159:96];
            end
        end
    end
endmodule
