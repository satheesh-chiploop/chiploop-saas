module temp_monitor_digital_regfile (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    control_enable,
    control_sample_start_pulse,
    control_irq_enable,
    control_alert_clear_pulse,
    irq_clear_alert_pulse,
    irq_clear_sample_done_pulse,
    threshold_code_reg,
    status_sample_done,
    status_alert_pending,
    status_adc_valid_seen,
    status_busy,
    irq_status_alert,
    irq_status_sample_done,
    latest_temp,
    sample_count,
    rd_data
);

input clk;
input reset_n;
input wr_en;
input [7:0] wr_addr;
input [15:0] wr_data;
input rd_en;
input [7:0] rd_addr;
output reg control_enable;
output reg control_sample_start_pulse;
output reg control_irq_enable;
output reg control_alert_clear_pulse;
output reg irq_clear_alert_pulse;
output reg irq_clear_sample_done_pulse;
output reg [11:0] threshold_code_reg;
input status_sample_done;
input status_alert_pending;
input status_adc_valid_seen;
input status_busy;
input irq_status_alert;
input irq_status_sample_done;
input [11:0] latest_temp;
input [15:0] sample_count;
output reg [15:0] rd_data;
localparam [7:0] REG_CONTROL     = 8'h00;
localparam [7:0] REG_STATUS      = 8'h04;
localparam [7:0] REG_THRESHOLD   = 8'h08;
localparam [7:0] REG_LATEST_TEMP = 8'h0C;
localparam [7:0] REG_SAMPLE_CNT  = 8'h10;
localparam [7:0] REG_IRQ_STATUS  = 8'h14;
localparam [7:0] REG_IRQ_CLEAR   = 8'h18;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        control_enable <= 1'b0;
        control_sample_start_pulse <= 1'b0;
        control_irq_enable <= 1'b0;
        control_alert_clear_pulse <= 1'b0;
        irq_clear_alert_pulse <= 1'b0;
        irq_clear_sample_done_pulse <= 1'b0;
        threshold_code_reg <= 12'h000;
        rd_data <= 16'h0000;
    end else begin
        control_sample_start_pulse <= 1'b0;
        control_alert_clear_pulse <= 1'b0;
        irq_clear_alert_pulse <= 1'b0;
        irq_clear_sample_done_pulse <= 1'b0;
        rd_data <= 16'h0000;

        if (wr_en) begin
            case (wr_addr)
                REG_CONTROL: begin
                    control_enable <= wr_data[0];
                    if (wr_data[1]) begin
                        control_sample_start_pulse <= 1'b1;
                    end
                    control_irq_enable <= wr_data[2];
                    if (wr_data[3]) begin
                        control_alert_clear_pulse <= 1'b1;
                    end
                end
                REG_THRESHOLD: begin
                    threshold_code_reg <= wr_data[11:0];
                end
                REG_IRQ_CLEAR: begin
                    if (wr_data[0]) begin
                        irq_clear_alert_pulse <= 1'b1;
                    end
                    if (wr_data[1]) begin
                        irq_clear_sample_done_pulse <= 1'b1;
                    end
                end
                default: begin
                end
            endcase
        end

        if (rd_en) begin
            case (rd_addr)
                REG_CONTROL: begin
                    rd_data <= {12'h000, control_irq_enable, 1'b0, control_enable, 1'b0};
                end
                REG_STATUS: begin
                    rd_data <= {12'h000, status_busy, status_adc_valid_seen, status_alert_pending, status_sample_done};
                end
                REG_THRESHOLD: begin
                    rd_data <= {4'h0, threshold_code_reg};
                end
                REG_LATEST_TEMP: begin
                    rd_data <= {4'h0, latest_temp};
                end
                REG_SAMPLE_CNT: begin
                    rd_data <= sample_count;
                end
                REG_IRQ_STATUS: begin
                    rd_data <= {14'h0000, irq_status_sample_done, irq_status_alert};
                end
                REG_IRQ_CLEAR: begin
                    rd_data <= 16'h0000;
                end
                default: begin
                    rd_data <= 16'h0000;
                end
            endcase
        end
    end
end

endmodule
