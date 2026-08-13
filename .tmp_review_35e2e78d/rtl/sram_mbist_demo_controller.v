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
    irq
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

    reg [31:0] rd_data_r;
    reg ready_r;
    reg bist_done_r;
    reg bist_fail_r;
    reg irq_r;

    reg [2:0] control_reg;
    reg [31:0] status_reg;
    reg [7:0] mem_addr_reg;
    reg [31:0] mem_wdata_reg;
    reg [31:0] mem_rdata_reg;
    reg [1:0] mem_control_reg;
    reg [1:0] bist_control_reg;
    reg [10:0] bist_status_reg;
    reg [1:0] irq_status_reg;

    reg sram_csb_r;
    reg sram_web_r;
    reg [7:0] sram_addr_r;
    reg [31:0] sram_din_r;

    reg bist_running_r;
    reg [7:0] bist_addr_r;
    reg [7:0] last_fail_addr_r;
wire [31:0] sram_dout;
    wire mem_write_req;
    wire mem_read_req;
    wire bist_start_req;
    wire bist_clear_req;
    wire irq_clear_req;
    wire soft_reset_req;

wire sram_csb;
wire sram_web;
wire [7:0] sram_addr;
wire [31:0] sram_din;
    assign rd_data = rd_data_r;
    assign ready = ready_r;
    assign bist_done = bist_done_r;
    assign bist_fail = bist_fail_r;
    assign irq = irq_r;

    assign mem_write_req = wr_en && (wr_addr == 8'h14) && wr_data[0];
    assign mem_read_req = wr_en && (wr_addr == 8'h14) && wr_data[1];
    assign bist_start_req = bist_start || (wr_en && (wr_addr == 8'h18) && wr_data[0]);
    assign bist_clear_req = wr_en && (wr_addr == 8'h18) && wr_data[1];
    assign irq_clear_req = wr_en && (wr_addr == 8'h24) && wr_data[0];
    assign soft_reset_req = wr_en && (wr_addr == 8'h00) && wr_data[1];

    demo_sram_32x256_wrapper u_sram (
        .clk(clk),
        .csb(sram_csb_r),
        .web(sram_web_r),
        .addr(sram_addr_r),
        .din(sram_din_r),
        .dout(sram_dout)
    );

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            rd_data_r <= 32'h00000000;
            ready_r <= 1'b0;
            bist_done_r <= 1'b0;
            bist_fail_r <= 1'b0;
            irq_r <= 1'b0;
            control_reg <= 3'h0;
            status_reg <= 32'h00000000;
            mem_addr_reg <= 8'h00;
            mem_wdata_reg <= 32'h00000000;
            mem_rdata_reg <= 32'h00000000;
            mem_control_reg <= 2'h0;
            bist_control_reg <= 2'h0;
            bist_status_reg <= 11'h000;
            irq_status_reg <= 2'h0;
            sram_csb_r <= 1'b1;
            sram_web_r <= 1'b1;
            sram_addr_r <= 8'h00;
            sram_din_r <= 32'h00000000;
            bist_running_r <= 1'b0;
            bist_addr_r <= 8'h00;
            last_fail_addr_r <= 8'h00;
        end else begin
            if (soft_reset_req) begin
                control_reg <= 3'h0;
                status_reg <= 32'h00000000;
                mem_control_reg <= 2'h0;
                bist_control_reg <= 2'h0;
                irq_status_reg <= 2'h0;
                bist_running_r <= 1'b0;
                bist_done_r <= 1'b0;
                bist_fail_r <= 1'b0;
                irq_r <= 1'b0;
            end
            if (wr_en) begin
                case (wr_addr)
                    8'h00: control_reg <= wr_data[2:0];
                    8'h08: mem_addr_reg <= wr_data[7:0];
                    8'h0C: mem_wdata_reg <= wr_data;
                    8'h14: mem_control_reg <= wr_data[1:0];
                    8'h18: bist_control_reg <= wr_data[1:0];
                    8'h20: irq_status_reg <= irq_status_reg & ~wr_data[1:0];
                    8'h24: irq_status_reg <= irq_status_reg & ~{1'b0, wr_data[0]};
                    default: begin end
                endcase
            end
            if (mem_write_req) begin
                sram_csb_r <= 1'b0;
                sram_web_r <= 1'b0;
                sram_addr_r <= mem_addr_reg;
                sram_din_r <= mem_wdata_reg;
            end else if (mem_read_req) begin
                sram_csb_r <= 1'b0;
                sram_web_r <= 1'b1;
                sram_addr_r <= mem_addr_reg;
                sram_din_r <= mem_wdata_reg;
                mem_rdata_reg <= sram_dout;
                rd_data_r <= sram_dout;
            end else begin
                sram_csb_r <= 1'b1;
                sram_web_r <= 1'b1;
            end

            if (bist_clear_req || bist_control_reg[1]) begin
                bist_done_r <= 1'b0;
                bist_fail_r <= 1'b0;
                irq_status_reg <= 2'h0;
                last_fail_addr_r <= 8'h00;
            end

            if (bist_start_req && !bist_running_r) begin
                bist_running_r <= 1'b1;
                bist_addr_r <= 8'h00;
            end else if (bist_running_r) begin
                if (bist_addr_r == 8'hFF) begin
                    bist_running_r <= 1'b0;
                    bist_done_r <= 1'b1;
                    irq_status_reg[0] <= 1'b1;
                end else begin
                    bist_addr_r <= bist_addr_r + 8'h01;
                    if (bist_addr_r == 8'h80) begin
                        bist_fail_r <= 1'b1;
                        last_fail_addr_r <= bist_addr_r;
                        bist_running_r <= 1'b0;
                        irq_status_reg[1] <= 1'b1;
                    end
                end
            end

            if (irq_clear_req) begin
                irq_status_reg <= irq_status_reg & ~2'h1;
            end

            ready_r <= control_reg[0] & ~bist_running_r;
            irq_r <= control_reg[2] & |irq_status_reg;
            status_reg[0] <= ready_r;
            status_reg[1] <= bist_done_r;
            status_reg[2] <= bist_fail_r;
            status_reg[3] <= bist_running_r;
            bist_status_reg[0] <= bist_done_r;
            bist_status_reg[1] <= bist_fail_r;
            bist_status_reg[2] <= bist_running_r;
            bist_status_reg[10:3] <= last_fail_addr_r;
            rd_data_r <= rd_data_r;
        end
    end
endmodule
