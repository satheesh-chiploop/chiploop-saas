module sram_mbist_demo_controller (
    input clk,
    input reset_n,
    input wr_en,
    input [7:0] wr_addr,
    input [31:0] wr_data,
    input rd_en,
    input [7:0] rd_addr,
    input bist_start,
    output reg [31:0] rd_data,
    output reg ready,
    output reg bist_done,
    output reg bist_fail,
    output reg irq
);

reg [31:0] control_reg;
reg [31:0] status_reg;
reg [7:0] mem_addr_reg;
reg [31:0] mem_wdata_reg;
reg [31:0] mem_rdata_reg;
reg [31:0] mem_control_reg;
reg [31:0] bist_control_reg;
reg [31:0] bist_status_reg;
reg [31:0] irq_status_reg;
reg [31:0] irq_clear_reg;

reg [7:0] last_fail_addr_reg;
reg busy_reg;
reg bist_running_reg;
reg mem_read_pending_reg;
reg [7:0] mem_read_addr_reg;
reg mem_read_valid_reg;
reg [31:0] mem_read_capture_reg;
reg bist_start_pending_reg;
reg bist_start_seen_reg;
reg bist_done_pulse_reg;
reg bist_fail_pulse_reg;
reg [7:0] bist_addr_reg;
reg [1:0] bist_state_reg;
reg [1:0] bist_next_state;
reg mem_write_req;
reg mem_read_req;
reg bist_clear_req;

wire demo_sram_32x256_wrapper_csb;
wire demo_sram_32x256_wrapper_web;
wire [7:0] demo_sram_32x256_wrapper_addr;
wire [31:0] demo_sram_32x256_wrapper_din;
wire [31:0] demo_sram_32x256_wrapper_dout;

localparam BIST_IDLE = 2'b00;
localparam BIST_RUN  = 2'b01;
localparam BIST_DONE = 2'b10;
localparam BIST_FAIL = 2'b11;

assign demo_sram_32x256_wrapper_csb = (control_reg[0] && (mem_write_req || mem_read_req || bist_running_reg)) ? 1'b0 : 1'b1;
assign demo_sram_32x256_wrapper_web = (mem_write_req) ? 1'b0 : 1'b1;
assign demo_sram_32x256_wrapper_addr = bist_running_reg ? bist_addr_reg : (mem_read_pending_reg ? mem_read_addr_reg : mem_addr_reg);
assign demo_sram_32x256_wrapper_din = mem_wdata_reg;

demo_sram_32x256_wrapper u_sram (
    .clk(clk),
    .csb(demo_sram_32x256_wrapper_csb),
    .web(demo_sram_32x256_wrapper_web),
    .addr(demo_sram_32x256_wrapper_addr),
    .din(demo_sram_32x256_wrapper_din),
    .dout(demo_sram_32x256_wrapper_dout)
);

always @(*) begin

    bist_status_reg = 32'b0;
    bist_status_reg[0] = bist_done;
    bist_status_reg[1] = bist_fail;
    bist_status_reg[2] = bist_running_reg;
    bist_status_reg[10:3] = last_fail_addr_reg;
    bist_status_reg[31:11] = 21'b0;

    irq = control_reg[2] && (irq_status_reg[0] || irq_status_reg[1]);
end

always @(*) begin
    mem_write_req = 1'b0;
    mem_read_req = 1'b0;
    bist_clear_req = 1'b0;
    bist_next_state = bist_state_reg;
    case (bist_state_reg)
        BIST_IDLE: begin
            if (bist_start || bist_control_reg[0] || bist_start_pending_reg) begin
                bist_next_state = BIST_RUN;
            end
        end
        BIST_RUN: begin
            if (bist_addr_reg == 8'hFF) begin
                bist_next_state = BIST_DONE;
            end
        end
        BIST_DONE: begin
            if (bist_clear_req) begin
                bist_next_state = BIST_IDLE;
            end
        end
        BIST_FAIL: begin
            if (bist_clear_req) begin
                bist_next_state = BIST_IDLE;
            end
        end
        default: begin
            bist_next_state = BIST_IDLE;
        end
    endcase
    if (control_reg[0] && wr_en) begin
        if (wr_addr == 8'h14) begin
            mem_write_req = wr_data[0];
            mem_read_req = wr_data[1];
        end
        if (wr_addr == 8'h18) begin
            bist_clear_req = wr_data[1];
        end
    end
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        control_reg <= 32'b0;
        mem_addr_reg <= 8'b0;
        mem_wdata_reg <= 32'b0;
        mem_rdata_reg <= 32'b0;
        mem_control_reg <= 32'b0;
        bist_control_reg <= 32'b0;
        irq_status_reg <= 32'b0;
        irq_clear_reg <= 32'b0;
        last_fail_addr_reg <= 8'b0;
        busy_reg <= 1'b0;
        bist_running_reg <= 1'b0;
        mem_read_pending_reg <= 1'b0;
        mem_read_addr_reg <= 8'b0;
        mem_read_valid_reg <= 1'b0;
        mem_read_capture_reg <= 32'b0;
        bist_start_pending_reg <= 1'b0;
        bist_start_seen_reg <= 1'b0;
        bist_done_pulse_reg <= 1'b0;
        bist_fail_pulse_reg <= 1'b0;
        bist_addr_reg <= 8'b0;
        bist_state_reg <= BIST_IDLE;
        rd_data <= 32'b0;
        ready <= 1'b0;
        bist_done <= 1'b0;
        bist_fail <= 1'b0;
    end else begin
        if (wr_en) begin
            case (wr_addr)
                8'h00: control_reg <= wr_data;
                8'h08: mem_addr_reg <= wr_data[7:0];
                8'h0C: mem_wdata_reg <= wr_data;
                8'h14: mem_control_reg <= wr_data;
                8'h18: bist_control_reg <= wr_data;
                8'h20: irq_status_reg <= irq_status_reg | wr_data[1:0];
                8'h24: irq_clear_reg <= wr_data;
                default: begin
                end
            endcase
        end

        if (wr_en && (wr_addr == 8'h24)) begin
            irq_status_reg[0] <= irq_status_reg[0] & ~wr_data[0];
            irq_status_reg[1] <= irq_status_reg[1] & ~wr_data[1];
        end

        if (wr_en && (wr_addr == 8'h18) && wr_data[1]) begin
            irq_status_reg <= 32'b0;
            bist_done_pulse_reg <= 1'b0;
            bist_fail_pulse_reg <= 1'b0;
        end

        if (bist_start) begin
            bist_start_pending_reg <= 1'b1;
        end

        if (wr_en && (wr_addr == 8'h18) && wr_data[0]) begin
            bist_start_pending_reg <= 1'b1;
        end

        if (control_reg[0] && wr_en && (wr_addr == 8'h14) && wr_data[0]) begin
            mem_read_pending_reg <= 1'b0;
        end

        if (control_reg[0] && wr_en && (wr_addr == 8'h14) && wr_data[1]) begin
            mem_read_pending_reg <= 1'b1;
            mem_read_addr_reg <= mem_addr_reg;
        end

        if (control_reg[0] && wr_en && (wr_addr == 8'h14) && wr_data[0]) begin
            mem_read_valid_reg <= 1'b0;
        end

        if (bist_state_reg == BIST_IDLE) begin
            if (bist_start || bist_control_reg[0] || bist_start_pending_reg) begin
                bist_running_reg <= 1'b1;
                bist_addr_reg <= 8'b0;
                bist_start_pending_reg <= 1'b0;
                bist_start_seen_reg <= 1'b1;
                bist_state_reg <= BIST_RUN;
            end
        end else if (bist_state_reg == BIST_RUN) begin
            bist_running_reg <= 1'b1;
            bist_addr_reg <= bist_addr_reg + 8'b1;
            if (bist_addr_reg == 8'hFF) begin
                bist_running_reg <= 1'b0;
                bist_done <= 1'b1;
                bist_fail <= 1'b0;
                last_fail_addr_reg <= 8'b0;
                irq_status_reg[0] <= 1'b1;
                bist_done_pulse_reg <= 1'b1;
                bist_state_reg <= BIST_DONE;
            end
        end else if (bist_state_reg == BIST_DONE) begin
            bist_running_reg <= 1'b0;
            if (bist_clear_req || bist_control_reg[1]) begin
                bist_done <= 1'b0;
                bist_fail <= 1'b0;
                irq_status_reg <= 32'b0;
                bist_done_pulse_reg <= 1'b0;
                bist_fail_pulse_reg <= 1'b0;
                bist_state_reg <= BIST_IDLE;
            end
        end else begin
            bist_running_reg <= 1'b0;
            if (bist_clear_req || bist_control_reg[1]) begin
                bist_done <= 1'b0;
                bist_fail <= 1'b0;
                irq_status_reg <= 32'b0;
                bist_done_pulse_reg <= 1'b0;
                bist_fail_pulse_reg <= 1'b0;
                bist_state_reg <= BIST_IDLE;
            end
        end

        if (control_reg[1]) begin
            control_reg[1] <= 1'b0;
            status_reg <= 32'b0;
            mem_rdata_reg <= 32'b0;
            rd_data <= 32'b0;
        end

        if (control_reg[0] && mem_write_req) begin
            mem_read_valid_reg <= 1'b0;
        end

        if (control_reg[0] && mem_read_req) begin
            mem_read_capture_reg <= demo_sram_32x256_wrapper_dout;
            mem_rdata_reg <= demo_sram_32x256_wrapper_dout;
            rd_data <= demo_sram_32x256_wrapper_dout;
            mem_read_valid_reg <= 1'b1;
        end

        if (rd_en) begin
            case (rd_addr)
                8'h00: rd_data <= control_reg;
                8'h04: rd_data <= status_reg;
                8'h08: rd_data <= {24'b0, mem_addr_reg};
                8'h0C: rd_data <= mem_wdata_reg;
                8'h10: rd_data <= mem_rdata_reg;
                8'h14: rd_data <= mem_control_reg;
                8'h18: rd_data <= bist_control_reg;
                8'h1C: rd_data <= bist_status_reg;
                8'h20: rd_data <= irq_status_reg;
                8'h24: rd_data <= irq_clear_reg;
                default: rd_data <= 32'b0;
            endcase
        end

        if (control_reg[0]) begin
            ready <= ~busy_reg;
        end else begin
            ready <= 1'b0;
        end

        busy_reg <= (bist_state_reg == BIST_RUN) | mem_read_pending_reg | mem_read_valid_reg | mem_write_req;
        if (mem_read_req) begin
            mem_read_pending_reg <= 1'b0;
        end
    end
end

endmodule
