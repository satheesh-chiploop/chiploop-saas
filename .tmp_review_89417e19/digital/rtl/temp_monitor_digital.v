module temp_monitor_digital (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    adc_code,
    adc_valid,
    rd_data,
    sample_req,
    alert_irq,
    temp_code,
    threshold_code,
    alert_status
);

input         clk;
input         reset_n;
input         wr_en;
input  [7:0] wr_addr;
input  [15:0] wr_data;
input         rd_en;
input  [7:0] rd_addr;
input  [11:0] adc_code;
input         adc_valid;

output [15:0] rd_data;
output        sample_req;
output        alert_irq;
output [11:0] temp_code;
output [11:0] threshold_code;
output        alert_status;

reg   [15:0] rd_data_r;
reg          sample_req_r;
reg          alert_irq_r;
reg   [11:0] temp_code_r;
reg   [11:0] threshold_code_r;
reg          alert_status_r;

reg          control_enable;
reg          control_irq_enable;

reg          status_sample_done;
reg          status_alert_pending;
reg          status_adc_valid_seen;
reg          status_busy;

reg   [11:0] latest_temp;
reg   [15:0] sample_count;

reg          irq_status_alert;
reg          irq_status_sample_done;

reg   [11:0] adc_sample_prev;
reg          adc_sample_prev_valid;

reg          sample_req_pending;
reg          sample_req_periodic_pulse;

reg   [11:0] filtered_temp;
reg   [11:0] next_filtered_temp;
reg   [11:0] threshold_compare_temp;
reg   [15:0] sample_count_next;

wire         alert_latched;
wire         sample_done_latched;
wire         request_sample;
wire         periodic_request;
wire         busy_next;
wire         alert_condition;

assign rd_data = rd_data_r;
assign sample_req = sample_req_r;
assign alert_irq = alert_irq_r;
assign temp_code = temp_code_r;
assign threshold_code = threshold_code_r;
assign alert_status = alert_status_r;

assign alert_latched = irq_status_alert;
assign sample_done_latched = irq_status_sample_done;
assign busy_next = sample_req_pending;
assign alert_condition = (threshold_compare_temp > threshold_code_r);
assign request_sample = sample_req_periodic_pulse;
assign periodic_request = sample_req_periodic_pulse;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        rd_data_r <= 16'h0000;
        sample_req_r <= 1'b0;
        alert_irq_r <= 1'b0;
        temp_code_r <= 12'h000;
        threshold_code_r <= 12'h000;
        alert_status_r <= 1'b0;

        control_enable <= 1'b0;
        control_irq_enable <= 1'b0;

        status_sample_done <= 1'b0;
        status_alert_pending <= 1'b0;
        status_adc_valid_seen <= 1'b0;
        status_busy <= 1'b0;

        latest_temp <= 12'h000;
        sample_count <= 16'h0000;

        irq_status_alert <= 1'b0;
        irq_status_sample_done <= 1'b0;

        adc_sample_prev <= 12'h000;
        adc_sample_prev_valid <= 1'b0;

        sample_req_pending <= 1'b0;
        sample_req_periodic_pulse <= 1'b0;

        filtered_temp <= 12'h000;
        next_filtered_temp <= 12'h000;
        threshold_compare_temp <= 12'h000;
        sample_count_next <= 16'h0000;
    end else begin
        sample_req_r <= 1'b0;
        sample_req_periodic_pulse <= 1'b0;

        if (wr_en) begin
            case (wr_addr)
                8'h00: begin
                    control_enable <= wr_data[0];
                    control_irq_enable <= wr_data[2];
                    if (wr_data[1]) begin
                        sample_req_r <= 1'b1;
                        sample_req_pending <= 1'b1;
                    end
                    if (wr_data[3]) begin
                        alert_status_r <= 1'b0;
                        status_alert_pending <= 1'b0;
                    end
                end

                8'h08: begin
                    threshold_code_r <= wr_data[11:0];
                end

                8'h18: begin
                    if (wr_data[0]) begin
                        irq_status_alert <= 1'b0;
                        alert_status_r <= 1'b0;
                        status_alert_pending <= 1'b0;
                    end
                    if (wr_data[1]) begin
                        irq_status_sample_done <= 1'b0;
                        status_sample_done <= 1'b0;
                    end
                end

                default: begin
                end
            endcase
        end

        if (sample_req_pending && !adc_valid) begin
            status_busy <= 1'b1;
        end else if (adc_valid) begin
            status_busy <= 1'b0;
            sample_req_pending <= 1'b0;
        end else if (control_enable) begin
            status_busy <= 1'b1;
            sample_req_periodic_pulse <= 1'b1;
            sample_req_r <= 1'b1;
            sample_req_pending <= 1'b1;
        end else begin
            status_busy <= 1'b0;
        end

        if (adc_valid) begin
            status_adc_valid_seen <= 1'b1;
            status_sample_done <= 1'b1;
            irq_status_sample_done <= 1'b1;

            if (adc_sample_prev_valid) begin
                filtered_temp <= (adc_sample_prev + adc_code) >> 1;
            end else begin
                filtered_temp <= adc_code;
            end

            if (adc_sample_prev_valid) begin
                next_filtered_temp <= (adc_sample_prev + adc_code) >> 1;
            end else begin
                next_filtered_temp <= adc_code;
            end

            latest_temp <= (adc_sample_prev_valid) ? ((adc_sample_prev + adc_code) >> 1) : adc_code;
            temp_code_r <= (adc_sample_prev_valid) ? ((adc_sample_prev + adc_code) >> 1) : adc_code;
            threshold_compare_temp <= (adc_sample_prev_valid) ? ((adc_sample_prev + adc_code) >> 1) : adc_code;
            sample_count_next <= sample_count + 16'h0001;
            sample_count <= sample_count + 16'h0001;

            if (((adc_sample_prev_valid) ? ((adc_sample_prev + adc_code) >> 1) : adc_code) > threshold_code_r) begin
                irq_status_alert <= 1'b1;
                alert_status_r <= 1'b1;
                status_alert_pending <= 1'b1;
            end

            adc_sample_prev <= adc_code;
            adc_sample_prev_valid <= 1'b1;
        end

        if (control_irq_enable && (irq_status_alert || irq_status_sample_done)) begin
            alert_irq_r <= 1'b1;
        end else begin
            alert_irq_r <= 1'b0;
        end

        if (sample_req_r) begin
            status_busy <= 1'b1;
        end

        if (adc_valid) begin
            sample_req_pending <= 1'b0;
        end
    end
end

always @(*) begin
    case (rd_addr)
        8'h00: begin
        end
        8'h04: begin
        end
        8'h08: begin
        end
        8'h0C: begin
        end
        8'h10: begin
        end
        8'h14: begin
        end
        8'h18: begin
        end
        default: begin
        end
    endcase
end

endmodule
