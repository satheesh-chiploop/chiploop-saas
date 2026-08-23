module adaptive_aero_req_fifo_wrapper (
    clk,
    rst_n,
    push_valid,
    push_data,
    push_ready,
    pop_valid,
    pop_data,
    pop_ready,
    level,
    mem_we,
    mem_addr,
    mem_din,
    mem_dout
);
    input         clk;
    input         rst_n;
    input         push_valid;
    input  [127:0] push_data;
    output        push_ready;
    input         pop_valid;
    output [127:0] pop_data;
    output        pop_ready;
    output [2:0] level;
    output        mem_we;
    output [1:0] mem_addr;
    output [127:0] mem_din;
    input  [127:0] mem_dout;
    reg [127:0] mem0;
    reg [127:0] mem1;
    reg [127:0] mem2;
    reg [127:0] mem3;

    reg [1:0] wr_ptr;
    reg [1:0] rd_ptr;
    reg [2:0] count;
    reg [127:0] pop_data_r;
    reg push_ready_r;
    reg pop_ready_r;
    reg mem_we_r;
    reg [1:0] mem_addr_r;
    reg [127:0] mem_din_r;
    assign push_ready = push_ready_r;
    assign pop_data = pop_data_r;
    assign pop_ready = pop_ready_r;
    assign level = count;
    assign mem_we = mem_we_r;
    assign mem_addr = mem_addr_r;
    assign mem_din = mem_din_r;

    always @(*) begin
        push_ready_r = 1'b0;
        pop_ready_r = 1'b0;
        mem_we_r = 1'b0;
        mem_addr_r = rd_ptr;
        mem_din_r = push_data;
        pop_data_r = mem_dout;

        if (count < 3'd4) begin
            push_ready_r = 1'b1;
        end
        if (count != 3'd0) begin
            pop_ready_r = 1'b1;
        end
        if (push_valid && push_ready_r) begin
            mem_we_r = 1'b1;
            mem_addr_r = wr_ptr;
            mem_din_r = push_data;
        end else if (pop_valid && pop_ready_r) begin
            mem_addr_r = rd_ptr;
        end else begin
            mem_addr_r = rd_ptr;
        end
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem0 <= 128'd0;
            mem1 <= 128'd0;
            mem2 <= 128'd0;
            mem3 <= 128'd0;
            wr_ptr <= 2'd0;
            rd_ptr <= 2'd0;
            count <= 3'd0;
        end else begin
            if (push_valid && push_ready_r) begin
                case (wr_ptr)
                    2'd0: mem0 <= push_data;
                    2'd1: mem1 <= push_data;
                    2'd2: mem2 <= push_data;
                    2'd3: mem3 <= push_data;
                    default: mem0 <= push_data;
                endcase
                wr_ptr <= wr_ptr + 2'd1;
                if (!(pop_valid && pop_ready_r)) begin
                    count <= count + 3'd1;
                end
            end
            if (pop_valid && pop_ready_r) begin
                case (rd_ptr)
                    2'd0: pop_data_r <= mem0;
                    2'd1: pop_data_r <= mem1;
                    2'd2: pop_data_r <= mem2;
                    2'd3: pop_data_r <= mem3;
                    default: pop_data_r <= mem0;
                endcase
                rd_ptr <= rd_ptr + 2'd1;
                if (!(push_valid && push_ready_r)) begin
                    count <= count - 3'd1;
                end
            end
        end
    end
endmodule
