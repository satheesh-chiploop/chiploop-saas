module temp_monitor_digital_sample_ctrl (
    clk,
    reset_n,
    control_enable,
    control_sample_start_pulse,
    control_irq_enable,
    control_alert_clear_pulse,
    irq_clear_alert_pulse,
    irq_clear_sample_done_pulse,
    threshold_code_reg,
    adc_code,
    adc_valid,
    sample_req,
    alert_irq,
    temp_code,
    alert_status,
    status_sample_done,
    status_alert_pending,
    status_adc_valid_seen,
    status_busy,
    irq_status_alert,
    irq_status_sample_done,
    latest_temp,
    sample_count,
    compare_alert,
    sample_done_pulse,
    sample_req_pulse
);

input clk;
input reset_n;
input control_enable;
input control_sample_start_pulse;
input control_irq_enable;
input control_alert_clear_pulse;
input irq_clear_alert_pulse;
input irq_clear_sample_done_pulse;
input [11:0] threshold_code_reg;
input [11:0] adc_code;
input adc_valid;
output reg sample_req;
output reg alert_irq;
output reg [11:0] temp_code;
output reg alert_status;
output reg status_sample_done;
output reg status_alert_pending;
output reg status_adc_valid_seen;
output reg status_busy;
output reg irq_status_alert;
output reg irq_status_sample_done;
output reg [11:0] latest_temp;
output reg [15:0] sample_count;
output reg compare_alert;
output reg sample_done_pulse;
output reg sample_req_pulse;

reg [11:0] sample_hist0;
reg [11:0] sample_hist1;
reg [12:0] avg_sum;
reg [11:0] avg_value;
reg [3:0] periodic_cnt;
reg pending_sample;
reg sample_req_int;
reg [12:0] avg_sum_next;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        sample_hist0 <= 12'h000;
        sample_hist1 <= 12'h000;
        avg_sum <= 13'h0000;
        avg_value <= 12'h000;
        periodic_cnt <= 4'h0;
        pending_sample <= 1'b0;
        sample_req_int <= 1'b0;
        sample_req <= 1'b0;
        alert_irq <= 1'b0;
        temp_code <= 12'h000;
        alert_status <= 1'b0;
        status_sample_done <= 1'b0;
        status_alert_pending <= 1'b0;
        status_adc_valid_seen <= 1'b0;
        status_busy <= 1'b0;
        irq_status_alert <= 1'b0;
        irq_status_sample_done <= 1'b0;
        latest_temp <= 12'h000;
        sample_count <= 16'h0000;
        compare_alert <= 1'b0;
        sample_done_pulse <= 1'b0;
        sample_req_pulse <= 1'b0;
        avg_sum_next <= 13'h0000;
    end else begin
        sample_req <= 1'b0;
        alert_irq <= control_irq_enable & (irq_status_alert | irq_status_sample_done);
        sample_req_int <= 1'b0;
        sample_req_pulse <= 1'b0;
        sample_done_pulse <= 1'b0;
        compare_alert <= 1'b0;

        if (control_alert_clear_pulse || irq_clear_alert_pulse) begin
            alert_status <= 1'b0;
            status_alert_pending <= 1'b0;
            irq_status_alert <= 1'b0;
        end

        if (irq_clear_sample_done_pulse) begin
            status_sample_done <= 1'b0;
            irq_status_sample_done <= 1'b0;
        end

        if (control_sample_start_pulse) begin
            sample_req_int <= 1'b1;
        end else if (control_enable && !pending_sample && !adc_valid) begin
            if (periodic_cnt == 4'h0) begin
                sample_req_int <= 1'b1;
                periodic_cnt <= 4'hF;
            end else begin
                periodic_cnt <= periodic_cnt - 4'h1;
            end
        end

        if (sample_req_int) begin
            sample_req <= 1'b1;
            sample_req_pulse <= 1'b1;
            pending_sample <= 1'b1;
        end

        if (adc_valid) begin
            avg_sum_next = {1'b0, adc_code} + {1'b0, sample_hist0};
            sample_hist1 <= sample_hist0;
            sample_hist0 <= adc_code;
            avg_sum <= avg_sum_next;
            avg_value <= avg_sum_next[12:1];
            latest_temp <= avg_sum_next[12:1];
            temp_code <= avg_sum_next[12:1];
            sample_count <= sample_count + 16'h0001;
            sample_done_pulse <= 1'b1;
            status_sample_done <= 1'b1;
            irq_status_sample_done <= 1'b1;
            status_adc_valid_seen <= 1'b1;
            pending_sample <= 1'b0;
            periodic_cnt <= 4'hF;
            compare_alert <= (avg_sum_next[12:1] > threshold_code_reg);
            if (avg_sum_next[12:1] > threshold_code_reg) begin
                alert_status <= 1'b1;
                status_alert_pending <= 1'b1;
                irq_status_alert <= 1'b1;
            end
        end

        if (control_enable && !pending_sample && !adc_valid && !control_sample_start_pulse) begin
            status_busy <= 1'b0;
        end else if (pending_sample) begin
            status_busy <= 1'b1;
        end else if (control_sample_start_pulse) begin
            status_busy <= 1'b1;
        end else if (adc_valid) begin
            status_busy <= 1'b0;
        end

        alert_irq <= control_irq_enable & (irq_status_alert | irq_status_sample_done);
    end
end

endmodule
