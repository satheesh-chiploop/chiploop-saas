module adaptive_aero_surrogate_reference (
    input         clk,
    input         reset_n,
    input         cfg_enable,
    input  [1:0] cfg_mode_select,
    input  [7:0] cfg_tilt_limit,
    input  [7:0] cfg_deflection_limit,
    input         response_valid,
    input  [127:0] response_data,
    input         response_stale,
    output reg [31:0] pack_vehicle_state,
    output reg [15:0] pack_wind_state,
    output reg [15:0] pack_reference_state,
    output reg [7:0] surrogate_tilt_cmd,
    output reg [7:0] surrogate_deflection_cmd,
    output reg [7:0] reference_tilt_cmd,
    output reg [7:0] reference_deflection_cmd,
    output reg        validation_valid,
    output reg        validation_error,
    output reg [7:0] validation_delta_code
);

reg [7:0] resp_tilt;
reg [7:0] resp_defl;
reg [7:0] ref_tilt_calc;
reg [7:0] ref_defl_calc;
reg [7:0] delta_tilt;
reg [7:0] delta_defl;

always @(*) begin
    resp_tilt = response_data[7:0];
    resp_defl = response_data[15:8];
    ref_tilt_calc = cfg_tilt_limit;
    ref_defl_calc = cfg_deflection_limit;
    delta_tilt = (resp_tilt > ref_tilt_calc) ? (resp_tilt - ref_tilt_calc) : (ref_tilt_calc - resp_tilt);
    delta_defl = (resp_defl > ref_defl_calc) ? (resp_defl - ref_defl_calc) : (ref_defl_calc - resp_defl);
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        pack_vehicle_state <= 32'd0;
        pack_wind_state <= 16'd0;
        pack_reference_state <= 16'd0;
        surrogate_tilt_cmd <= 8'd0;
        surrogate_deflection_cmd <= 8'd0;
        reference_tilt_cmd <= 8'd0;
        reference_deflection_cmd <= 8'd0;
        validation_valid <= 1'b0;
        validation_error <= 1'b0;
        validation_delta_code <= 8'd0;
    end else begin
        pack_vehicle_state <= response_data[31:0];
        pack_wind_state <= response_data[47:32];
        pack_reference_state <= response_data[63:48];
        surrogate_tilt_cmd <= response_data[7:0];
        surrogate_deflection_cmd <= response_data[15:8];
        reference_tilt_cmd <= cfg_tilt_limit;
        reference_deflection_cmd <= cfg_deflection_limit;
        validation_valid <= cfg_enable && response_valid && !response_stale && (delta_tilt <= cfg_tilt_limit) && (delta_defl <= cfg_deflection_limit);
        validation_error <= response_stale || (response_valid && ((delta_tilt > cfg_tilt_limit) || (delta_defl > cfg_deflection_limit) || (cfg_mode_select == 2'b11)));
        validation_delta_code <= delta_tilt | delta_defl;
    end
end

endmodule
