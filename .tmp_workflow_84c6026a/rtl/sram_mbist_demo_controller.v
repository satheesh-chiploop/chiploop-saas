module sram_mbist_demo_controller (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    bist_start,
    rd_data,
    ready,
    bist_done,
    bist_fail,
    irq,
    mem_csb,
    mem_web,
    mem_addr,
    mem_din,
    mem_dout,
    bist_request,
    irq_enable
);
input clk;
input reset_n;
input wr_en;
input [7:0] wr_addr;
input [31:0] wr_data;
input rd_en;
input [7:0] rd_addr;
input bist_start;
output [31:0] rd_data;
output ready;
output bist_done;
output bist_fail;
output irq;
output mem_csb;
output mem_web;
output [5:0] mem_addr;
output [31:0] mem_din;
input [31:0] mem_dout;
output bist_request;
output irq_enable;

reg [31:0] rd_data_r;
reg ready_r;
reg bist_done_r;
reg bist_fail_r;
reg irq_r;
reg mem_csb_r;
reg mem_web_r;
reg [5:0] mem_addr_r;
reg [31:0] mem_din_r;
reg bist_request_r;
reg irq_enable_r;

reg [2:0] control_reg;
reg [5:0] mem_addr_reg;
reg [31:0] mem_wdata_reg;
reg [31:0] mem_rdata_reg;
reg [1:0] mem_control_reg;
reg [1:0] bist_control_reg;
reg [5:0] bist_last_fail_addr_reg;
reg [1:0] irq_status_reg;

reg bist_running_r;
reg bist_busy_r;

reg [31:0] read_mux;

assign rd_data = rd_data_r;
assign ready = ready_r;
assign bist_done = bist_done_r;
assign bist_fail = bist_fail_r;
assign irq = irq_r;
assign mem_csb = mem_csb_r;
assign mem_web = mem_web_r;
assign mem_addr = mem_addr_r;
assign mem_din = mem_din_r;
assign bist_request = bist_request_r;
assign irq_enable = irq_enable_r;

wire software_reset_pulse;
wire control_enable;
wire control_irq_enable;
wire mem_write_pulse;
wire mem_read_pulse;
wire bist_clear_pulse;
wire bist_start_req;
wire irq_clear_done_pulse;
wire irq_clear_fail_pulse;
wire irq_latched_done;
wire irq_latched_fail;

assign software_reset_pulse = wr_en && (wr_addr == 8'h00) && wr_data[1];
assign control_enable = control_reg[0];
assign control_irq_enable = control_reg[2];
assign mem_write_pulse = wr_en && (wr_addr == 8'h14) && wr_data[0];
assign mem_read_pulse = wr_en && (wr_addr == 8'h14) && wr_data[1];
assign bist_clear_pulse = wr_en && (wr_addr == 8'h18) && wr_data[1];
assign bist_start_req = bist_start || (wr_en && (wr_addr == 8'h18) && wr_data[0]);
assign irq_clear_done_pulse = wr_en && (wr_addr == 8'h24) && wr_data[0];
assign irq_clear_fail_pulse = wr_en && (wr_addr == 8'h24) && wr_data[1];
assign irq_latched_done = irq_status_reg[0];
assign irq_latched_fail = irq_status_reg[1];

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        control_reg <= 3'b000;
        mem_addr_reg <= 6'b000000;
        mem_wdata_reg <= 32'h00000000;
        mem_rdata_reg <= 32'h00000000;
        mem_control_reg <= 2'b00;
        bist_control_reg <= 2'b00;
        bist_last_fail_addr_reg <= 6'b000000;
        irq_status_reg <= 2'b00;
        bist_running_r <= 1'b0;
        bist_busy_r <= 1'b0;
        ready_r <= 1'b0;
        bist_done_r <= 1'b0;
        bist_fail_r <= 1'b0;
        irq_r <= 1'b0;
        mem_csb_r <= 1'b1;
        mem_web_r <= 1'b1;
        mem_addr_r <= 6'b000000;
        mem_din_r <= 32'h00000000;
        bist_request_r <= 1'b0;
        irq_enable_r <= 1'b0;
        rd_data_r <= 32'h00000000;
    end else begin
        if (software_reset_pulse) begin
            control_reg <= 3'b000;
            mem_addr_reg <= 6'b000000;
            mem_wdata_reg <= 32'h00000000;
            mem_rdata_reg <= 32'h00000000;
            mem_control_reg <= 2'b00;
            bist_control_reg <= 2'b00;
            bist_last_fail_addr_reg <= 6'b000000;
            irq_status_reg <= 2'b00;
            bist_running_r <= 1'b0;
            bist_busy_r <= 1'b0;
            ready_r <= 1'b0;
            bist_done_r <= 1'b0;
            bist_fail_r <= 1'b0;
            irq_r <= 1'b0;
            mem_csb_r <= 1'b1;
            mem_web_r <= 1'b1;
            mem_addr_r <= 6'b000000;
            mem_din_r <= 32'h00000000;
            bist_request_r <= 1'b0;
            irq_enable_r <= 1'b0;
            rd_data_r <= 32'h00000000;
        end else begin
            if (wr_en) begin
                case (wr_addr)
                    8'h00: begin
                        control_reg <= wr_data[2:0];
                    end
                    8'h08: begin
                        mem_addr_reg <= wr_data[5:0];
                    end
                    8'h0C: begin
                        mem_wdata_reg <= wr_data;
                    end
                    8'h14: begin
                        mem_control_reg <= wr_data[1:0];
                    end
                    8'h18: begin
                        bist_control_reg <= wr_data[1:0];
                    end
                    8'h24: begin
                        if (wr_data[0]) begin
                            irq_status_reg[0] <= 1'b0;
                        end
                        if (wr_data[1]) begin
                            irq_status_reg[1] <= 1'b0;
                        end
                    end
                    default: begin
                    end
                endcase
            end

            if (mem_write_pulse) begin
                mem_csb_r <= 1'b0;
                mem_web_r <= 1'b0;
                mem_addr_r <= mem_addr_reg;
                mem_din_r <= mem_wdata_reg;
                bist_busy_r <= 1'b0;
            end else if (mem_read_pulse) begin
                mem_csb_r <= 1'b0;
                mem_web_r <= 1'b1;
                mem_addr_r <= mem_addr_reg;
                mem_din_r <= mem_wdata_reg;
                mem_rdata_reg <= mem_dout;
                bist_busy_r <= 1'b0;
            end else begin
                mem_csb_r <= 1'b1;
                mem_web_r <= 1'b1;
                mem_addr_r <= mem_addr_reg;
                mem_din_r <= mem_wdata_reg;
            end

            if (bist_start_req) begin
                bist_request_r <= 1'b1;
                bist_running_r <= 1'b1;
                bist_busy_r <= 1'b1;
                bist_done_r <= 1'b0;
                bist_fail_r <= 1'b0;
            end else begin
                bist_request_r <= 1'b0;
            end

            if (bist_clear_pulse) begin
                bist_done_r <= 1'b0;
                bist_fail_r <= 1'b0;
                irq_status_reg <= 2'b00;
                bist_last_fail_addr_reg <= 6'b000000;
                irq_r <= 1'b0;
            end

            if (irq_clear_done_pulse) begin
                irq_status_reg[0] <= 1'b0;
            end
            if (irq_clear_fail_pulse) begin
                irq_status_reg[1] <= 1'b0;
            end

            if (control_reg[1]) begin
                control_reg[1] <= 1'b0;
            end

            irq_enable_r <= control_reg[2];
            ready_r <= control_reg[0] & ~bist_busy_r;
            bist_done_r <= bist_done_r;
            bist_fail_r <= bist_fail_r;
            irq_r <= (control_reg[2] & (irq_status_reg[0] | irq_status_reg[1]));

            if (bist_busy_r && !bist_done_r) begin
                bist_done_r <= 1'b1;
                bist_running_r <= 1'b0;
                bist_busy_r <= 1'b0;
                irq_status_reg[0] <= 1'b1;
            end

            if (bist_busy_r && wr_en && (wr_addr == 8'h1C) && wr_data[1]) begin
                bist_fail_r <= 1'b1;
                bist_last_fail_addr_reg <= mem_addr_reg;
                bist_running_r <= 1'b0;
                bist_busy_r <= 1'b0;
                irq_status_reg[1] <= 1'b1;
            end

            if (rd_en) begin
                case (rd_addr)
                    8'h00: read_mux = {29'b00000000000000000000000000000, control_reg};
                    8'h04: read_mux = {28'b0000000000000000000000000000, bist_busy_r, bist_fail_r, bist_done_r, ready_r};
                    8'h08: read_mux = {26'b00000000000000000000000000, mem_addr_reg};
                    8'h0C: read_mux = mem_wdata_reg;
                    8'h10: read_mux = mem_rdata_reg;
                    8'h14: read_mux = {30'b000000000000000000000000000000, mem_control_reg};
                    8'h18: read_mux = {30'b000000000000000000000000000000, bist_control_reg};
                    8'h1C: read_mux = {23'b00000000000000000000000, bist_last_fail_addr_reg, bist_busy_r, bist_fail_r, bist_done_r};
                    8'h20: read_mux = {30'b000000000000000000000000000000, irq_status_reg};
                    8'h24: read_mux = {30'b000000000000000000000000000000, 2'b00};
                    default: read_mux = 32'h00000000;
                endcase
                rd_data_r <= read_mux;
            end else begin
                rd_data_r <= 32'h00000000;
            end
        end
    end
end

endmodule
