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

input clk;
input reset_n;
input wr_en;
input [7:0] wr_addr;
input [15:0] wr_data;
input rd_en;
input [7:0] rd_addr;
input [11:0] adc_code;
input adc_valid;

output [15:0] rd_data;
output sample_req;
output alert_irq;
output [11:0] temp_code;
output [11:0] threshold_code;
output alert_status;

reg [15:0] rd_data_r;
reg sample_req_r;
reg alert_irq_r;
reg [11:0] temp_code_r;
reg [11:0] threshold_code_r;
reg alert_status_r;

reg enable_reg;
reg irq_enable_reg;
reg busy_reg;
reg status_sample_done;
reg status_alert_pending;
reg adc_valid_seen;
reg irq_status_alert;
reg irq_status_sample_done;
reg [15:0] sample_count;
reg [11:0] latest_temp;
reg [11:0] threshold_reg;
reg [11:0] prev_adc_code;
reg prev_sample_valid;
reg [1:0] periodic_div;

wire sample_start_pulse;
wire alert_clear_pulse;
wire irq_clear_alert_pulse;
wire irq_clear_sample_pulse;
wire sample_complete;
wire alert_condition;
wire periodic_pulse;
wire [12:0] avg_sum;
wire [11:0] filtered_temp;
wire [15:0] status_read;
wire [15:0] threshold_read;
wire [15:0] latest_temp_read;
wire [15:0] sample_count_read;
wire [15:0] irq_status_read;
wire [15:0] control_read;
wire [15:0] irq_clear_write;

assign sample_start_pulse = wr_en && (wr_addr == 8'h00) && wr_data[1];
assign alert_clear_pulse = wr_en && (wr_addr == 8'h00) && wr_data[3];
assign irq_clear_alert_pulse = wr_en && (wr_addr == 8'h18) && wr_data[0];
assign irq_clear_sample_pulse = wr_en && (wr_addr == 8'h18) && wr_data[1];
assign sample_complete = adc_valid;
assign alert_condition = sample_complete && (filtered_temp > threshold_reg);
assign periodic_pulse = enable_reg && (periodic_div == 2'b00);

assign avg_sum = {1'b0, adc_code} + {1'b0, prev_adc_code};
assign filtered_temp = avg_sum[12:1];

assign control_read = {12'b0, irq_enable_reg, 1'b0, enable_reg, 1'b0};
assign status_read = {12'b0, busy_reg, adc_valid_seen, status_alert_pending, status_sample_done};
assign threshold_read = {4'b0, threshold_reg};
assign latest_temp_read = {4'b0, latest_temp};
assign sample_count_read = sample_count;
assign irq_status_read = {14'b0, irq_status_sample_done, irq_status_alert};
assign irq_clear_write = {14'b0, wr_data[1:0]};

assign rd_data = rd_data_r;
assign sample_req = sample_req_r;
assign alert_irq = alert_irq_r;
assign temp_code = temp_code_r;
assign threshold_code = threshold_code_r;
assign alert_status = alert_status_r;

always @(*) begin
    rd_data_r = 16'h0000;
    case (rd_addr)
        8'h00: rd_data_r = control_read;
        8'h04: rd_data_r = status_read;
        8'h08: rd_data_r = threshold_read;
        8'h0C: rd_data_r = latest_temp_read;
        8'h10: rd_data_r = sample_count_read;
        8'h14: rd_data_r = irq_status_read;
        8'h18: rd_data_r = 16'h0000;
        default: rd_data_r = 16'h0000;
    endcase
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        enable_reg <= 1'b0;
        irq_enable_reg <= 1'b0;
        busy_reg <= 1'b0;
        status_sample_done <= 1'b0;
        status_alert_pending <= 1'b0;
        adc_valid_seen <= 1'b0;
        irq_status_alert <= 1'b0;
        irq_status_sample_done <= 1'b0;
        sample_count <= 16'h0000;
        latest_temp <= 12'h000;
        threshold_reg <= 12'h000;
        prev_adc_code <= 12'h000;
        prev_sample_valid <= 1'b0;
        periodic_div <= 2'b00;
        sample_req_r <= 1'b0;
        alert_irq_r <= 1'b0;
        temp_code_r <= 12'h000;
        threshold_code_r <= 12'h000;
        alert_status_r <= 1'b0;
    end else begin
        sample_req_r <= 1'b0;

        if (periodic_div == 2'b00) begin
            periodic_div <= 2'b01;
        end else begin
            periodic_div <= periodic_div + 2'b01;
        end

        if (wr_en && (wr_addr == 8'h00)) begin
            enable_reg <= wr_data[0];
            irq_enable_reg <= wr_data[2];
            if (wr_data[1]) begin
                sample_req_r <= 1'b1;
            end
            if (wr_data[3]) begin
                alert_status_r <= 1'b0;
                status_alert_pending <= 1'b0;
                irq_status_alert <= 1'b0;
            end
        end

        if (wr_en && (wr_addr == 8'h08)) begin
            threshold_reg <= wr_data[11:0];
        end

        if (wr_en && (wr_addr == 8'h18)) begin
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

        if (sample_start_pulse) begin
            sample_req_r <= 1'b1;
            busy_reg <= 1'b1;
        end else if (periodic_pulse) begin
            sample_req_r <= 1'b1;
            busy_reg <= 1'b1;
        end

        if (sample_complete) begin
            prev_adc_code <= adc_code;
            prev_sample_valid <= 1'b1;
            adc_valid_seen <= 1'b1;
            latest_temp <= filtered_temp;
            temp_code_r <= filtered_temp;
            threshold_code_r <= threshold_reg;
            sample_count <= sample_count + 16'h0001;
            status_sample_done <= 1'b1;
            irq_status_sample_done <= 1'b1;
            busy_reg <= 1'b0;
            if (filtered_temp > threshold_reg) begin
                alert_status_r <= 1'b1;
                status_alert_pending <= 1'b1;
                irq_status_alert <= 1'b1;
            end
        end

        if (alert_clear_pulse) begin
            alert_status_r <= 1'b0;
            status_alert_pending <= 1'b0;
            irq_status_alert <= 1'b0;
        end

        if (irq_clear_alert_pulse) begin
            irq_status_alert <= 1'b0;
            alert_status_r <= 1'b0;
            status_alert_pending <= 1'b0;
        end

        if (irq_clear_sample_pulse) begin
            irq_status_sample_done <= 1'b0;
            status_sample_done <= 1'b0;
        end

        if (prev_sample_valid) begin
            temp_code_r <= latest_temp;
        end else begin
            temp_code_r <= 12'h000;
        end

        threshold_code_r <= threshold_reg;
        alert_irq_r <= irq_enable_reg && (irq_status_alert || irq_status_sample_done);
    end
end

endmodule
