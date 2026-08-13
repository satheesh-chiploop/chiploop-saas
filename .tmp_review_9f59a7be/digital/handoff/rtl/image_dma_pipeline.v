module image_dma_pipeline (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    dma_rd_data,
    dma_rd_valid,
    dma_wr_ready,
    rd_data,
    dma_rd_req,
    dma_rd_addr,
    dma_wr_req,
    dma_wr_addr,
    dma_wr_data,
    irq,
    frame_active,
    frame_done,
    pixel_valid,
    pixel_out,
    histogram_bin,
    histogram_count
);
input clk;
input reset_n;
input wr_en;
input [11:0] wr_addr;
input [31:0] wr_data;
input rd_en;
input [11:0] rd_addr;
input [31:0] dma_rd_data;
input dma_rd_valid;
input dma_wr_ready;
output [31:0] rd_data;
output reg dma_rd_req;
output reg [31:0] dma_rd_addr;
output reg dma_wr_req;
output reg [31:0] dma_wr_addr;
output reg [31:0] dma_wr_data;
output reg irq;
output reg frame_active;
output reg frame_done;
output reg pixel_valid;
output reg [7:0] pixel_out;
output reg [7:0] histogram_bin;
output reg [15:0] histogram_count;
reg [31:0] rd_data_r;
assign rd_data = rd_data_r;

reg [7:0] control_reg;
reg [31:0] src_base_reg;
reg [31:0] dst_base_reg;
reg [31:0] width_reg;
reg [31:0] height_reg;
reg [31:0] stride_reg;
reg [7:0] filter_mode_reg;
reg [8:0] brightness_reg;
reg [7:0] contrast_reg;
reg [7:0] threshold_reg;
reg [31:0] irq_status_reg;
reg [31:0] pixel_count_reg;
reg [31:0] frame_count_reg;
reg [31:0] error_status_reg;
reg [7:0] kernel0_reg;
reg [7:0] kernel1_reg;
reg [7:0] kernel2_reg;
reg [7:0] kernel3_reg;
reg [7:0] kernel4_reg;
reg [7:0] kernel5_reg;
reg [7:0] kernel6_reg;
reg [7:0] kernel7_reg;
reg [7:0] kernel8_reg;

reg [7:0] linebuf0 [0:255];
reg [7:0] linebuf1 [0:255];
reg [7:0] linebuf2 [0:255];

reg [7:0] pixel_fifo0;
reg [7:0] pixel_fifo1;
reg [7:0] pixel_fifo2;
reg [7:0] pixel_fifo3;
reg [1:0] fifo_count;

reg [7:0] x_coord_reg;
reg [7:0] y_coord_reg;
reg [7:0] line_count_reg;
reg [1:0] stage_valid0;
reg [1:0] stage_valid1;
reg [1:0] stage_valid2;
reg [1:0] stage_valid3;
reg [1:0] stage_valid4;
reg [1:0] stage_valid5;
reg [7:0] window00;
reg [7:0] window01;
reg [7:0] window02;
reg [7:0] window10;
reg [7:0] window11;
reg [7:0] window12;
reg [7:0] window20;
reg [7:0] window21;
reg [7:0] window22;

reg [15:0] histogram_mem [0:255];

reg [31:0] dma_rd_addr_next;
reg [31:0] dma_wr_addr_next;
reg [31:0] dma_wr_data_next;
reg dma_rd_req_next;
reg dma_wr_req_next;
reg [31:0] rd_data_next;
reg irq_next;
reg frame_active_next;
reg frame_done_next;
reg pixel_valid_next;
reg [7:0] pixel_out_next;
reg [7:0] histogram_bin_next;
reg [15:0] histogram_count_next;

reg [7:0] pixel_in;
reg [7:0] conv_sum0;
reg [15:0] conv_sum1;
reg [15:0] conv_sum2;
reg [15:0] conv_sum3;
reg [15:0] conv_sum4;
reg [15:0] conv_sum5;
reg [15:0] conv_sum6;
reg [15:0] conv_sum7;
reg [15:0] conv_sum8;
reg [15:0] conv_acc;
reg [15:0] adjusted_value;
reg [7:0] saturated_value;
reg [7:0] packed_pixel0;
reg [7:0] packed_pixel1;
reg [7:0] packed_pixel2;
reg [7:0] packed_pixel3;
reg [1:0] pack_index_reg;
reg [31:0] rd_mux;
reg [15:0] hist_current;
reg [15:0] hist_next;
reg [15:0] hist_bin_value;
reg [31:0] addr_calc;
reg [31:0] word_index_reg;
reg [31:0] pixel_base_count;
reg [31:0] expected_pixels;
reg busy_reg;
reg histogram_done_reg;
reg dma_rd_busy_reg;
reg dma_wr_busy_reg;

integer i;

localparam ADDR_CONTROL      = 12'h000;
localparam ADDR_STATUS       = 12'h004;
localparam ADDR_SRC_BASE     = 12'h008;
localparam ADDR_DST_BASE     = 12'h00C;
localparam ADDR_WIDTH        = 12'h010;
localparam ADDR_HEIGHT       = 12'h014;
localparam ADDR_STRIDE       = 12'h018;
localparam ADDR_FILTER_MODE  = 12'h01C;
localparam ADDR_BRIGHTNESS   = 12'h020;
localparam ADDR_CONTRAST     = 12'h024;
localparam ADDR_THRESHOLD    = 12'h028;
localparam ADDR_IRQ_STATUS   = 12'h02C;
localparam ADDR_IRQ_CLEAR    = 12'h030;
localparam ADDR_PIXEL_COUNT  = 12'h034;
localparam ADDR_FRAME_COUNT  = 12'h038;
localparam ADDR_ERROR_STATUS = 12'h03C;

always @(*) begin
    rd_data_r = 32'h00000000;
    case (rd_addr)
        ADDR_CONTROL:      rd_data_r = {24'h000000, control_reg};
        ADDR_STATUS:       rd_data_r = {26'h0000000, histogram_done_reg, error_status_reg[0], dma_wr_busy_reg, dma_rd_busy_reg, frame_done, busy_reg};
        ADDR_SRC_BASE:     rd_data_r = src_base_reg;
        ADDR_DST_BASE:     rd_data_r = dst_base_reg;
        ADDR_WIDTH:        rd_data_r = width_reg;
        ADDR_HEIGHT:       rd_data_r = height_reg;
        ADDR_STRIDE:       rd_data_r = stride_reg;
        ADDR_FILTER_MODE:  rd_data_r = {24'h000000, filter_mode_reg};
        ADDR_BRIGHTNESS:   rd_data_r = {23'h000000, brightness_reg};
        ADDR_CONTRAST:     rd_data_r = {24'h000000, contrast_reg};
        ADDR_THRESHOLD:    rd_data_r = {24'h000000, threshold_reg};
        ADDR_IRQ_STATUS:   rd_data_r = irq_status_reg;
        ADDR_PIXEL_COUNT:  rd_data_r = pixel_count_reg;
        ADDR_FRAME_COUNT:  rd_data_r = frame_count_reg;
        ADDR_ERROR_STATUS: rd_data_r = error_status_reg;
        default:           rd_data_r = 32'h00000000;
    endcase
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        control_reg <= 8'h00;
        src_base_reg <= 32'h00000000;
        dst_base_reg <= 32'h00000000;
        width_reg <= 32'd256;
        height_reg <= 32'd0;
        stride_reg <= 32'd1024;
        filter_mode_reg <= 8'h00;
        brightness_reg <= 9'h000;
        contrast_reg <= 8'h01;
        threshold_reg <= 8'h80;
        irq_status_reg <= 32'h00000000;
        pixel_count_reg <= 32'h00000000;
        frame_count_reg <= 32'h00000000;
        error_status_reg <= 32'h00000000;
        kernel0_reg <= 8'sd0;
        kernel1_reg <= 8'sd0;
        kernel2_reg <= 8'sd0;
        kernel3_reg <= 8'sd0;
        kernel4_reg <= 8'sd0;
        kernel5_reg <= 8'sd0;
        kernel6_reg <= 8'sd0;
        kernel7_reg <= 8'sd0;
        kernel8_reg <= 8'sd0;
        dma_rd_req <= 1'b0;
        dma_rd_addr <= 32'h00000000;
        dma_wr_req <= 1'b0;
        dma_wr_addr <= 32'h00000000;
        dma_wr_data <= 32'h00000000;
        irq <= 1'b0;
        frame_active <= 1'b0;
        frame_done <= 1'b0;
        pixel_valid <= 1'b0;
        pixel_out <= 8'h00;
        histogram_bin <= 8'h00;
        histogram_count <= 16'h0000;
        fifo_count <= 2'b00;
        pixel_fifo0 <= 8'h00;
        pixel_fifo1 <= 8'h00;
        pixel_fifo2 <= 8'h00;
        pixel_fifo3 <= 8'h00;
        x_coord_reg <= 8'h00;
        y_coord_reg <= 8'h00;
        line_count_reg <= 8'h00;
        stage_valid0 <= 2'b00;
        stage_valid1 <= 2'b00;
        stage_valid2 <= 2'b00;
        stage_valid3 <= 2'b00;
        stage_valid4 <= 2'b00;
        stage_valid5 <= 2'b00;
        window00 <= 8'h00;
        window01 <= 8'h00;
        window02 <= 8'h00;
        window10 <= 8'h00;
        window11 <= 8'h00;
        window12 <= 8'h00;
        window20 <= 8'h00;
        window21 <= 8'h00;
        window22 <= 8'h00;
        busy_reg <= 1'b0;
        histogram_done_reg <= 1'b0;
        dma_rd_busy_reg <= 1'b0;
        dma_wr_busy_reg <= 1'b0;
        for (i = 0; i < 256; i = i + 1) begin
            linebuf0[i] <= 8'h00;
            linebuf1[i] <= 8'h00;
            linebuf2[i] <= 8'h00;
            histogram_mem[i] <= 16'h0000;
        end
    end else begin
        if (wr_en) begin
            case (wr_addr)
                ADDR_CONTROL: begin
                    control_reg <= wr_data[7:0];
                    if (wr_data[2]) begin
                        control_reg <= 8'h00;
                        src_base_reg <= 32'h00000000;
                        dst_base_reg <= 32'h00000000;
                        width_reg <= 32'd256;
                        height_reg <= 32'd0;
                        stride_reg <= 32'd1024;
                        filter_mode_reg <= 8'h00;
                        brightness_reg <= 9'h000;
                        contrast_reg <= 8'h01;
                        threshold_reg <= 8'h80;
                        irq_status_reg <= 32'h00000000;
                        pixel_count_reg <= 32'h00000000;
                        frame_count_reg <= 32'h00000000;
                        error_status_reg <= 32'h00000000;
                        dma_rd_req <= 1'b0;
                        dma_wr_req <= 1'b0;
                        dma_rd_addr <= 32'h00000000;
                        dma_wr_addr <= 32'h00000000;
                        dma_wr_data <= 32'h00000000;
                        irq <= 1'b0;
                        frame_active <= 1'b0;
                        frame_done <= 1'b0;
                        pixel_valid <= 1'b0;
                        pixel_out <= 8'h00;
                        histogram_bin <= 8'h00;
                        histogram_count <= 16'h0000;
                        fifo_count <= 2'b00;
                        busy_reg <= 1'b0;
                        histogram_done_reg <= 1'b0;
                        dma_rd_busy_reg <= 1'b0;
                        dma_wr_busy_reg <= 1'b0;
                    end
                end
                ADDR_SRC_BASE: src_base_reg <= wr_data;
                ADDR_DST_BASE: dst_base_reg <= wr_data;
                ADDR_WIDTH: width_reg <= wr_data;
                ADDR_HEIGHT: height_reg <= wr_data;
                ADDR_STRIDE: stride_reg <= wr_data;
                ADDR_FILTER_MODE: filter_mode_reg <= wr_data[7:0];
                ADDR_BRIGHTNESS: brightness_reg <= wr_data[8:0];
                ADDR_CONTRAST: contrast_reg <= wr_data[7:0];
                ADDR_THRESHOLD: threshold_reg <= wr_data[7:0];
                ADDR_IRQ_CLEAR: irq_status_reg <= irq_status_reg & ~wr_data;
                12'h100: kernel0_reg <= wr_data[7:0];
                12'h104: kernel1_reg <= wr_data[7:0];
                12'h108: kernel2_reg <= wr_data[7:0];
                12'h10C: kernel3_reg <= wr_data[7:0];
                12'h110: kernel4_reg <= wr_data[7:0];
                12'h114: kernel5_reg <= wr_data[7:0];
                12'h118: kernel6_reg <= wr_data[7:0];
                12'h11C: kernel7_reg <= wr_data[7:0];
                12'h120: kernel8_reg <= wr_data[7:0];
                default: begin
                end
            endcase
        end

        if (control_reg[1] && control_reg[0] && !busy_reg) begin
            busy_reg <= 1'b1;
            frame_active <= 1'b1;
            frame_done <= 1'b0;
            pixel_count_reg <= 32'h00000000;
            histogram_done_reg <= 1'b0;
            dma_rd_busy_reg <= 1'b1;
            dma_wr_busy_reg <= 1'b1;
            dma_rd_req <= 1'b1;
            dma_wr_req <= 1'b0;
            dma_rd_addr <= src_base_reg;
            dma_wr_addr <= dst_base_reg;
        end

        if (dma_rd_valid) begin
            pixel_fifo0 <= dma_rd_data[7:0];
            pixel_fifo1 <= dma_rd_data[15:8];
            pixel_fifo2 <= dma_rd_data[23:16];
            pixel_fifo3 <= dma_rd_data[31:24];
            fifo_count <= 2'b11;
            stage_valid0 <= 2'b01;
            stage_valid1 <= 2'b01;
            stage_valid2 <= 2'b01;
            stage_valid3 <= 2'b01;
            stage_valid4 <= 2'b01;
            stage_valid5 <= 2'b01;
            x_coord_reg <= x_coord_reg + 8'd4;
            pixel_base_count <= pixel_count_reg + 32'd4;
            pixel_count_reg <= pixel_count_reg + 32'd4;
            histogram_bin <= dma_rd_data[7:0];
            hist_current <= histogram_mem[dma_rd_data[7:0]];
            if (hist_current != 16'hFFFF) begin
                histogram_mem[dma_rd_data[7:0]] <= hist_current + 16'h0001;
            end
            histogram_count <= histogram_mem[dma_rd_data[7:0]];
        end

        if (busy_reg) begin
            addr_calc <= src_base_reg + (y_coord_reg * stride_reg) + (x_coord_reg[7:2] << 2);
            dma_rd_addr <= addr_calc;
            dma_rd_req <= control_reg[0];
            dma_rd_busy_reg <= control_reg[0];
            if (dma_wr_ready) begin
                dma_wr_req <= 1'b1;
                dma_wr_addr <= dst_base_reg + (y_coord_reg * stride_reg) + (x_coord_reg[7:2] << 2);
                dma_wr_data <= dma_wr_data_next;
                dma_wr_busy_reg <= 1'b0;
            end else begin
                dma_wr_req <= 1'b0;
                dma_wr_busy_reg <= 1'b1;
            end
        end else begin
            dma_rd_req <= 1'b0;
            dma_wr_req <= 1'b0;
            dma_rd_busy_reg <= 1'b0;
            dma_wr_busy_reg <= 1'b0;
        end

        window00 <= linebuf0[x_coord_reg];
        window01 <= linebuf0[x_coord_reg + 8'd1];
        window02 <= linebuf0[x_coord_reg + 8'd2];
        window10 <= linebuf1[x_coord_reg];
        window11 <= linebuf1[x_coord_reg + 8'd1];
        window12 <= linebuf1[x_coord_reg + 8'd2];
        window20 <= linebuf2[x_coord_reg];
        window21 <= linebuf2[x_coord_reg + 8'd1];
        window22 <= linebuf2[x_coord_reg + 8'd2];

        conv_sum0 <= $signed(kernel0_reg) * $signed(window00);
        conv_sum1 <= $signed(kernel1_reg) * $signed(window01);
        conv_sum2 <= $signed(kernel2_reg) * $signed(window02);
        conv_sum3 <= $signed(kernel3_reg) * $signed(window10);
        conv_sum4 <= $signed(kernel4_reg) * $signed(window11);
        conv_sum5 <= $signed(kernel5_reg) * $signed(window12);
        conv_sum6 <= $signed(kernel6_reg) * $signed(window20);
        conv_sum7 <= $signed(kernel7_reg) * $signed(window21);
        conv_sum8 <= $signed(kernel8_reg) * $signed(window22);
        conv_acc <= conv_sum0 + conv_sum1 + conv_sum2 + conv_sum3 + conv_sum4 + conv_sum5 + conv_sum6 + conv_sum7 + conv_sum8;
        adjusted_value <= conv_acc + {{7{brightness_reg[8]}}, brightness_reg};
        if (adjusted_value[15:8] != 8'h00 && adjusted_value[15] == 1'b0) begin
            saturated_value <= 8'hFF;
        end else if (adjusted_value[15]) begin
            saturated_value <= 8'h00;
        end else begin
            saturated_value <= adjusted_value[7:0] * contrast_reg;
        end
        if (filter_mode_reg == 8'd4) begin
            if (saturated_value >= threshold_reg) begin
                pixel_out <= 8'hFF;
            end else begin
                pixel_out <= 8'h00;
            end
        end else begin
            pixel_out <= saturated_value;
        end
        pixel_valid <= busy_reg && (fifo_count != 2'b00);
        histogram_bin <= pixel_out;
        hist_bin_value <= histogram_mem[pixel_out];
        if (hist_bin_value != 16'hFFFF) begin
            histogram_mem[pixel_out] <= hist_bin_value + 16'h0001;
        end
        histogram_count <= histogram_mem[pixel_out];
        dma_wr_data <= {pixel_out, pixel_out, pixel_out, pixel_out};
        dma_wr_data_next <= {pixel_out, pixel_out, pixel_out, pixel_out};
        if (pixel_count_reg >= (width_reg * height_reg) && busy_reg) begin
            busy_reg <= 1'b0;
            frame_active <= 1'b0;
            frame_done <= 1'b1;
            frame_count_reg <= frame_count_reg + 32'd1;
            histogram_done_reg <= 1'b1;
            irq_status_reg[0] <= 1'b1;
            irq_status_reg[1] <= 1'b1;
            irq_status_reg[2] <= 1'b1;
        end
        if (frame_done && control_reg[3]) begin
            irq <= 1'b1;
        end else if (irq_status_reg != 32'h00000000 && control_reg[3]) begin
            irq <= 1'b1;
        end else begin
            irq <= 1'b0;
        end
        if (busy_reg) begin
            linebuf0[x_coord_reg] <= pixel_fifo0;
            linebuf1[x_coord_reg] <= pixel_fifo1;
            linebuf2[x_coord_reg] <= pixel_fifo2;
        end
    end
end

always @(*) begin
    dma_rd_addr_next = dma_rd_addr;
    dma_wr_addr_next = dma_wr_addr;
    dma_rd_req_next = dma_rd_req;
    dma_wr_req_next = dma_wr_req;
    rd_data_next = rd_data_r;
    irq_next = irq;
    frame_active_next = frame_active;
    frame_done_next = frame_done;
    pixel_valid_next = pixel_valid;
    pixel_out_next = pixel_out;
    histogram_bin_next = histogram_bin;
    histogram_count_next = histogram_count;
end

endmodule
