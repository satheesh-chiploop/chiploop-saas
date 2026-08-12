module temp_sensor_adc_model (
    input        sample_req,
    input  [15:0] sensor_temp_celsius,
    input        avdd,
    input        avss,
    output reg [11:0] adc_code,
    output reg       adc_valid
);

    parameter integer GAIN_ERROR = 0;
    parameter integer OFFSET_ERROR = 0;
    parameter integer NOMINAL_SAMPLE_LATENCY = 1;

    reg [11:0] latched_adc_code;
    reg        latched_adc_valid;
    reg [31:0] conversion_timer;
    reg        request_active;
    reg [31:0] temp_ext;
    reg [31:0] scaled_temp;
    reg signed [31:0] temp_signed;
    reg signed [31:0] code_signed;
    reg signed [31:0] code_with_err;
    reg signed [31:0] gain_adjust;
    reg signed [31:0] offset_adjust;

    always @(*) begin
        temp_ext = {16'b0, sensor_temp_celsius};
        temp_signed = $signed({1'b0, sensor_temp_celsius});

        gain_adjust = $signed(GAIN_ERROR);
        offset_adjust = $signed(OFFSET_ERROR);

        scaled_temp = temp_ext << 2;

        code_signed = temp_signed * 16'sd4;
        code_with_err = code_signed + (code_signed * gain_adjust) / 1000000 + offset_adjust;

        if (code_with_err < 0)
            code_with_err = 0;
        else if (code_with_err > 4095)
            code_with_err = 4095;
    end

    always @(posedge sample_req or posedge avdd or posedge avss) begin
        if (sample_req) begin
            request_active <= 1'b1;
            if (NOMINAL_SAMPLE_LATENCY <= 0)
                conversion_timer <= 32'd0;
            else
                conversion_timer <= NOMINAL_SAMPLE_LATENCY[31:0];
        end
    end

    always @(*) begin
        if (NOMINAL_SAMPLE_LATENCY <= 0) begin
            latched_adc_code = code_with_err[11:0];
            latched_adc_valid = request_active;
        end else begin
            latched_adc_code = adc_code;
            latched_adc_valid = 1'b0;
        end
    end

    always @(posedge sample_req or posedge avdd or posedge avss) begin
        if (sample_req) begin
            adc_code <= adc_code;
            adc_valid <= 1'b0;
        end
    end

    initial begin
        adc_code <= 12'd0;
        adc_valid <= 1'b0;
        latched_adc_code = 12'd0;
        latched_adc_valid = 1'b0;
        conversion_timer <= 32'd0;
        request_active <= 1'b0;
        temp_ext = 32'd0;
        scaled_temp = 32'd0;
        temp_signed = 32'sd0;
        code_signed = 32'sd0;
        code_with_err = 32'sd0;
        gain_adjust = 32'sd0;
        offset_adjust = 32'sd0;
    end


endmodule
