module ag_response_parser(
    clk,
    rst_n,
    i_model_response,
    request_id_expected,
    model_valid_in,
    response_timeout,
    model_data_valid,
    response_error,
    stale_detected,
    response_age,
    drag_force,
    lift_force,
    surface_pressure,
    flow_field_meta
);
input clk;
input rst_n;
input [191:0] i_model_response;
input [15:0] request_id_expected;
input model_valid_in;
input [15:0] response_timeout;
output model_data_valid;
output response_error;
output stale_detected;
output [15:0] response_age;
output [31:0] drag_force;
output [31:0] lift_force;
output [31:0] surface_pressure;
output [63:0] flow_field_meta;
reg model_data_valid_r;
reg response_error_r;
reg stale_detected_r;
reg [15:0] response_age_r;
reg [31:0] drag_force_r;
reg [31:0] lift_force_r;
reg [31:0] surface_pressure_r;
reg [63:0] flow_field_meta_r;
wire [15:0] resp_request_id;
wire [15:0] resp_age;
wire packet_complete;
wire request_match;
wire stale_now;

assign resp_request_id = i_model_response[15:0];
assign resp_age = i_model_response[31:16];
assign packet_complete = model_valid_in & i_model_response[191];
assign request_match = (resp_request_id == request_id_expected);
assign stale_now = (resp_age > response_timeout) | (~request_match) | (~model_valid_in);

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        model_data_valid_r <= 1'b0;
        response_error_r <= 1'b0;
        stale_detected_r <= 1'b0;
        response_age_r <= 16'h0000;
        drag_force_r <= 32'h00000000;
        lift_force_r <= 32'h00000000;
        surface_pressure_r <= 32'h00000000;
        flow_field_meta_r <= 64'h0000000000000000;
    end else begin
        response_age_r <= resp_age;
        stale_detected_r <= stale_detected_r | stale_now;
        response_error_r <= (~packet_complete) | (~request_match);
        model_data_valid_r <= packet_complete & request_match & ~stale_now;
        if (packet_complete & request_match & ~stale_now) begin
            drag_force_r <= i_model_response[63:32];
            lift_force_r <= i_model_response[95:64];
            surface_pressure_r <= i_model_response[127:96];
            flow_field_meta_r <= i_model_response[191:128];
        end
    end
end

assign model_data_valid = model_data_valid_r;
assign response_error = response_error_r;
assign stale_detected = stale_detected_r;
assign response_age = response_age_r;
assign drag_force = drag_force_r;
assign lift_force = lift_force_r;
assign surface_pressure = surface_pressure_r;
assign flow_field_meta = flow_field_meta_r;

endmodule
