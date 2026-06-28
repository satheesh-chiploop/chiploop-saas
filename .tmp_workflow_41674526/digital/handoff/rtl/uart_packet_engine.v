module uart_packet_engine (
    clk,
    reset_n,
    wr_en,
    wr_addr,
    wr_data,
    rd_en,
    rd_addr,
    uart_rx,
    rd_data,
    uart_tx,
    irq,
    rx_fifo_level,
    tx_fifo_level,
    packet_count
);
    input clk;
    input reset_n;
    input wr_en;
    input [7:0] wr_addr;
    input [7:0] wr_data;
    input rd_en;
    input [7:0] rd_addr;
    input uart_rx;
    output [7:0] rd_data;
    output uart_tx;
    output irq;
    output [5:0] rx_fifo_level;
    output [5:0] tx_fifo_level;
    output [15:0] packet_count;
    reg [7:0] rd_data_r;
    reg uart_tx_r;
    reg irq_r;
    reg [5:0] rx_fifo_level_r;
    reg [5:0] tx_fifo_level_r;
    reg [15:0] packet_count_r;
    reg [7:0] control_reg;
    reg [15:0] baud_div_reg;
    reg [7:0] packet_len_reg;
    reg [7:0] irq_status_reg;

    reg [7:0] tx_fifo_mem [0:15];
    reg [7:0] rx_fifo_mem [0:15];
    reg [3:0] tx_wr_ptr;
    reg [3:0] tx_rd_ptr;
    reg [3:0] rx_wr_ptr;
    reg [3:0] rx_rd_ptr;
    reg [4:0] tx_count;
    reg [4:0] rx_count;

    reg [15:0] baud_cnt;
    reg baud_tick;

    reg [3:0] tx_bit_cnt;
    reg [3:0] rx_bit_cnt;
    reg [7:0] tx_shift;
    reg [7:0] rx_shift;
    reg [3:0] tx_state;
    reg [3:0] rx_state;
    reg [7:0] tx_hold_byte;
    reg tx_hold_valid;
    reg [7:0] loopback_byte;
    reg loopback_valid;
    reg [7:0] rx_sample_cnt;

    reg tx_busy_r;
    reg rx_busy_r;
    reg packet_active_r;
    reg error_r;

    localparam TXS_IDLE = 4'd0;
    localparam TXS_START = 4'd1;
    localparam TXS_DATA = 4'd2;
    localparam TXS_STOP = 4'd3;

    localparam RXS_IDLE = 4'd0;
    localparam RXS_START = 4'd1;
    localparam RXS_DATA = 4'd2;
    localparam RXS_STOP = 4'd3;

    wire enable;
    wire rx_enable;
    wire tx_enable;
    wire loopback;
    wire irq_enable;

    wire tx_empty;
    wire tx_full;
    wire rx_empty;
    wire rx_full;

    assign enable = control_reg[0];
    assign rx_enable = control_reg[1];
    assign tx_enable = control_reg[2];
    assign loopback = control_reg[3];
    assign irq_enable = control_reg[4];

    assign tx_empty = (tx_count == 5'd0);
    assign tx_full = (tx_count == 5'd16);
    assign rx_empty = (rx_count == 5'd0);
    assign rx_full = (rx_count == 5'd16);

    assign rd_data = rd_data_r;
    assign uart_tx = uart_tx_r;
    assign irq = irq_r;
    assign rx_fifo_level = rx_fifo_level_r;
    assign tx_fifo_level = tx_fifo_level_r;
    assign packet_count = packet_count_r;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            rd_data_r <= 8'h00;
            uart_tx_r <= 1'b1;
            irq_r <= 1'b0;
            rx_fifo_level_r <= 6'd0;
            tx_fifo_level_r <= 6'd0;
            packet_count_r <= 16'd0;
            control_reg <= 8'h00;
            baud_div_reg <= 16'h0000;
            packet_len_reg <= 8'h00;
            irq_status_reg <= 8'h00;
            tx_wr_ptr <= 4'd0;
            tx_rd_ptr <= 4'd0;
            rx_wr_ptr <= 4'd0;
            rx_rd_ptr <= 4'd0;
            tx_count <= 5'd0;
            rx_count <= 5'd0;
            baud_cnt <= 16'd0;
            baud_tick <= 1'b0;
            tx_bit_cnt <= 4'd0;
            rx_bit_cnt <= 4'd0;
            tx_shift <= 8'h00;
            rx_shift <= 8'h00;
            tx_state <= TXS_IDLE;
            rx_state <= RXS_IDLE;
            tx_hold_byte <= 8'h00;
            tx_hold_valid <= 1'b0;
            loopback_byte <= 8'h00;
            loopback_valid <= 1'b0;
            rx_sample_cnt <= 8'h00;
            tx_busy_r <= 1'b0;
            rx_busy_r <= 1'b0;
            packet_active_r <= 1'b0;
            error_r <= 1'b0;
        end else begin
            baud_tick <= 1'b0;
            if (baud_div_reg == 16'd0) begin
                baud_cnt <= 16'd0;
                baud_tick <= 1'b1;
            end else if (baud_cnt == (baud_div_reg - 16'd1)) begin
                baud_cnt <= 16'd0;
                baud_tick <= 1'b1;
            end else begin
                baud_cnt <= baud_cnt + 16'd1;
            end

            if (wr_en) begin
                case (wr_addr)
                    8'h00: control_reg <= wr_data & 8'h1F;
                    8'h04: baud_div_reg[7:0] <= wr_data;
                    8'h05: baud_div_reg[15:8] <= wr_data;
                    8'h08: packet_len_reg <= wr_data;
                    8'h0C: begin
                        if (enable && tx_enable) begin
                            if (!tx_full) begin
                                tx_fifo_mem[tx_wr_ptr] <= wr_data;
                                tx_wr_ptr <= tx_wr_ptr + 4'd1;
                                tx_count <= tx_count + 5'd1;
                            end else begin
                                irq_status_reg[2] <= 1'b1;
                                error_r <= 1'b1;
                            end
                        end else begin
                            irq_status_reg[2] <= 1'b1;
                            error_r <= 1'b1;
                        end
                    end
                    8'h1C: begin
                        irq_status_reg <= irq_status_reg & ~wr_data[5:0];
                    end
                    default: begin
                    end
                endcase
            end

            if (rd_en) begin
                case (rd_addr)
                    8'h00: rd_data_r <= control_reg & 8'h1F;
                    8'h04: rd_data_r <= baud_div_reg[7:0];
                    8'h05: rd_data_r <= baud_div_reg[15:8];
                    8'h08: rd_data_r <= packet_len_reg;
                    8'h10: begin
                        if (!rx_empty) begin
                            rd_data_r <= rx_fifo_mem[rx_rd_ptr];
                            rx_rd_ptr <= rx_rd_ptr + 4'd1;
                            rx_count <= rx_count - 5'd1;
                        end else begin
                            rd_data_r <= 8'h00;
                        end
                    end
                    8'h14: begin
                        rd_data_r[0] <= tx_empty;
                        rd_data_r[1] <= tx_full;
                        rd_data_r[2] <= rx_empty;
                        rd_data_r[3] <= rx_full;
                        rd_data_r[4] <= tx_busy_r;
                        rd_data_r[5] <= rx_busy_r;
                        rd_data_r[6] <= packet_active_r;
                        rd_data_r[7] <= error_r;
                    end
                    8'h18: rd_data_r <= irq_status_reg;
                    8'h20: rd_data_r <= packet_count_r[7:0];
                    8'h21: rd_data_r <= packet_count_r[15:8];
                    default: rd_data_r <= 8'h00;
                endcase
            end else begin
                rd_data_r <= rd_data_r;
            end

            if (baud_tick) begin
                case (tx_state)
                    TXS_IDLE: begin
                        uart_tx_r <= 1'b1;
                        tx_busy_r <= 1'b0;
                        if (enable && tx_enable && !tx_empty) begin
                            tx_hold_byte <= tx_fifo_mem[tx_rd_ptr];
                            tx_rd_ptr <= tx_rd_ptr + 4'd1;
                            tx_count <= tx_count - 5'd1;
                            tx_shift <= tx_fifo_mem[tx_rd_ptr];
                            tx_bit_cnt <= 4'd0;
                            tx_state <= TXS_START;
                            tx_busy_r <= 1'b1;
                            packet_active_r <= 1'b1;
                        end else if (enable && tx_enable && tx_empty) begin
                            irq_status_reg[3] <= 1'b1;
                            error_r <= 1'b1;
                        end
                    end
                    TXS_START: begin
                        uart_tx_r <= 1'b0;
                        tx_state <= TXS_DATA;
                        tx_bit_cnt <= 4'd0;
                    end
                    TXS_DATA: begin
                        uart_tx_r <= tx_shift[0];
                        tx_shift <= {1'b0, tx_shift[7:1]};
                        if (tx_bit_cnt == 4'd7) begin
                            tx_state <= TXS_STOP;
                        end
                        tx_bit_cnt <= tx_bit_cnt + 4'd1;
                    end
                    TXS_STOP: begin
                        uart_tx_r <= 1'b1;
                        tx_state <= TXS_IDLE;
                        tx_busy_r <= 1'b0;
                        if (packet_len_reg != 8'h00) begin
                            packet_count_r <= packet_count_r + 16'd1;
                            if (packet_count_r[7:0] + 8'd1 == packet_len_reg) begin
                                irq_status_reg[1] <= 1'b1;
                                irq_status_reg[5] <= 1'b1;
                            end
                        end
                        if (loopback) begin
                            loopback_byte <= tx_hold_byte;
                            loopback_valid <= 1'b1;
                        end
                    end
                    default: begin
                        tx_state <= TXS_IDLE;
                    end
                endcase
            end

            if (loopback_valid) begin
                if (enable && rx_enable) begin
                    if (!rx_full) begin
                        rx_fifo_mem[rx_wr_ptr] <= loopback_byte;
                        rx_wr_ptr <= rx_wr_ptr + 4'd1;
                        rx_count <= rx_count + 5'd1;
                        packet_count_r <= packet_count_r + 16'd1;
                        irq_status_reg[0] <= 1'b1;
                        if (packet_len_reg != 8'h00) begin
                            if (packet_count_r[7:0] + 8'd1 == packet_len_reg) begin
                                irq_status_reg[5] <= 1'b1;
                            end
                        end
                    end else begin
                        irq_status_reg[2] <= 1'b1;
                        error_r <= 1'b1;
                    end
                end
                loopback_valid <= 1'b0;
            end

            if (enable && rx_enable && uart_rx == 1'b0 && rx_state == RXS_IDLE && baud_tick) begin
                rx_state <= RXS_START;
                rx_sample_cnt <= 8'd0;
                rx_busy_r <= 1'b1;
            end else if (baud_tick) begin
                case (rx_state)
                    RXS_START: begin
                        if (uart_rx == 1'b0) begin
                            rx_state <= RXS_DATA;
                            rx_bit_cnt <= 4'd0;
                            rx_shift <= 8'h00;
                        end else begin
                            rx_state <= RXS_IDLE;
                            rx_busy_r <= 1'b0;
                            irq_status_reg[4] <= 1'b1;
                            error_r <= 1'b1;
                        end
                    end
                    RXS_DATA: begin
                        rx_shift <= {uart_rx, rx_shift[7:1]};
                        if (rx_bit_cnt == 4'd7) begin
                            rx_state <= RXS_STOP;
                        end
                        rx_bit_cnt <= rx_bit_cnt + 4'd1;
                    end
                    RXS_STOP: begin
                        if (uart_rx == 1'b1) begin
                            if (enable && rx_enable) begin
                                if (!rx_full) begin
                                    rx_fifo_mem[rx_wr_ptr] <= rx_shift;
                                    rx_wr_ptr <= rx_wr_ptr + 4'd1;
                                    rx_count <= rx_count + 5'd1;
                                    packet_count_r <= packet_count_r + 16'd1;
                                    irq_status_reg[0] <= 1'b1;
                                    if (packet_len_reg != 8'h00) begin
                                        if (packet_count_r[7:0] + 8'd1 == packet_len_reg) begin
                                            irq_status_reg[0] <= 1'b1;
                                            irq_status_reg[5] <= 1'b1;
                                        end
                                    end
                                end else begin
                                    irq_status_reg[2] <= 1'b1;
                                    error_r <= 1'b1;
                                end
                            end
                        end else begin
                            irq_status_reg[4] <= 1'b1;
                            error_r <= 1'b1;
                        end
                        rx_state <= RXS_IDLE;
                        rx_busy_r <= 1'b0;
                    end
                    default: begin
                        rx_state <= RXS_IDLE;
                        rx_busy_r <= 1'b0;
                    end
                endcase
            end

            if ((irq_status_reg[0] | irq_status_reg[1]) && packet_len_reg != 8'h00) begin
                packet_active_r <= 1'b1;
            end
            if (tx_empty && rx_empty && (tx_state == TXS_IDLE) && (rx_state == RXS_IDLE)) begin
                packet_active_r <= 1'b0;
            end

            if (irq_status_reg != 8'h00) begin
                irq_r <= irq_enable;
            end else begin
                irq_r <= 1'b0;
            end

            rx_fifo_level_r <= {1'b0, rx_count};
            tx_fifo_level_r <= {1'b0, tx_count};
            if (error_r) begin
                irq_status_reg[7] <= 1'b1;
            end
        end
    end
endmodule
