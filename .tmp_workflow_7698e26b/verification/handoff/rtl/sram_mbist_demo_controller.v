module sram_mbist_demo_controller (
    input clk,
    input reset_n,
    input wr_en,
    input [7:0] wr_addr,
    input [31:0] wr_data,
    input rd_en,
    input [7:0] rd_addr,
    input bist_start,
    output [31:0] rd_data,
    output ready,
    output bist_done,
    output bist_fail,
    output irq
);
    reg [31:0] control_reg;
    reg [31:0] mem_addr_reg;
    reg [31:0] mem_wdata_reg;
    reg [31:0] mem_rdata_reg;
    reg [31:0] mem_control_reg;
    reg [31:0] bist_control_reg;
    reg [31:0] bist_status_reg;
    reg [31:0] irq_status_reg;
    reg [7:0] last_fail_addr_reg;
    reg busy_reg;
    reg [31:0] rd_data_r;
    wire [31:0] demo_sram_32x256_wrapper_dout;
    wire [31:0] demo_sram_32x256_model_dout;
    wire demo_sram_32x256_wrapper_csb;
    wire demo_sram_32x256_wrapper_web;
    wire [7:0] demo_sram_32x256_wrapper_addr;
    wire [31:0] demo_sram_32x256_wrapper_din;
    wire demo_sram_32x256_model_csb;
    wire demo_sram_32x256_model_web;
    wire [7:0] demo_sram_32x256_model_addr;
    wire [31:0] demo_sram_32x256_model_din;

    assign ready = reset_n & ~busy_reg;
    assign bist_done = bist_status_reg[0];
    assign bist_fail = bist_status_reg[1];
    assign irq = control_reg[2] & (irq_status_reg[0] | irq_status_reg[1]);
    assign rd_data = rd_data_r;

    assign demo_sram_32x256_wrapper_csb = 1'b1;
    assign demo_sram_32x256_wrapper_web = 1'b1;
    assign demo_sram_32x256_wrapper_addr = mem_addr_reg[7:0];
    assign demo_sram_32x256_wrapper_din = mem_wdata_reg;

    assign demo_sram_32x256_model_csb = demo_sram_32x256_wrapper_csb;
    assign demo_sram_32x256_model_web = demo_sram_32x256_wrapper_web;
    assign demo_sram_32x256_model_addr = demo_sram_32x256_wrapper_addr;
    assign demo_sram_32x256_model_din = demo_sram_32x256_wrapper_din;

    demo_sram_32x256_wrapper u_sram (
        .clk(clk),
        .csb(demo_sram_32x256_wrapper_csb),
        .web(demo_sram_32x256_wrapper_web),
        .addr(demo_sram_32x256_wrapper_addr),
        .din(demo_sram_32x256_wrapper_din),
        .dout(demo_sram_32x256_wrapper_dout)
    );

    demo_sram_32x256_model u_sram_model (
        .clk(clk),
        .csb(demo_sram_32x256_model_csb),
        .web(demo_sram_32x256_model_web),
        .addr(demo_sram_32x256_model_addr),
        .din(demo_sram_32x256_model_din),
        .dout(demo_sram_32x256_model_dout)
    );

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            control_reg <= 32'h00000000;
            mem_addr_reg <= 32'h00000000;
            mem_wdata_reg <= 32'h00000000;
            mem_rdata_reg <= 32'h00000000;
            mem_control_reg <= 32'h00000000;
            bist_control_reg <= 32'h00000000;
            bist_status_reg <= 32'h00000000;
            irq_status_reg <= 32'h00000000;
            last_fail_addr_reg <= 8'h00;
            busy_reg <= 1'b0;
            rd_data_r <= 32'h00000000;
        end else begin
            if (wr_en) begin
                case (wr_addr)
                    8'h00: control_reg <= {29'b00000000000000000000000000000, wr_data[2:0]};
                    8'h08: mem_addr_reg <= {24'h000000, wr_data[7:0]};
                    8'h0C: mem_wdata_reg <= wr_data;
                    8'h14: mem_control_reg <= {30'b000000000000000000000000000000, wr_data[1:0]};
                    8'h18: begin
                        bist_control_reg <= {30'b000000000000000000000000000000, wr_data[1:0]};
                        if (wr_data[0]) begin
                            bist_status_reg[0] <= 1'b1;
                            busy_reg <= 1'b1;
                        end
                        if (wr_data[1]) begin
                            bist_status_reg <= 32'h00000000;
                            irq_status_reg <= 32'h00000000;
                        end
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

            if (bist_start) begin
                bist_status_reg[0] <= 1'b1;
                busy_reg <= 1'b1;
                bist_control_reg[0] <= 1'b1;
            end

            if (rd_en) begin
                case (rd_addr)
                    8'h00: rd_data_r <= control_reg;
                    8'h04: rd_data_r <= {28'h0000000, busy_reg, bist_fail, bist_done, ready};
                    8'h08: rd_data_r <= {24'h000000, mem_addr_reg[7:0]};
                    8'h0C: rd_data_r <= mem_wdata_reg;
                    8'h10: rd_data_r <= mem_rdata_reg;
                    8'h14: rd_data_r <= {30'h00000000, mem_control_reg[1:0]};
                    8'h18: rd_data_r <= {30'h00000000, bist_control_reg[1:0]};
                    8'h1C: rd_data_r <= {21'h000000, last_fail_addr_reg[7:0], busy_reg, bist_status_reg[2], bist_fail, bist_done};
                    8'h20: rd_data_r <= {30'h00000000, irq_status_reg[1:0]};
                    default: rd_data_r <= 32'h00000000;
                endcase
            end

            if (mem_control_reg[1] & control_reg[0]) begin
                mem_rdata_reg <= demo_sram_32x256_wrapper_dout;
                busy_reg <= 1'b0;
                mem_control_reg[1] <= 1'b0;
            end

            if (bist_status_reg[0] & busy_reg) begin
                bist_status_reg[2] <= 1'b0;
            end
        end
    end
endmodule
