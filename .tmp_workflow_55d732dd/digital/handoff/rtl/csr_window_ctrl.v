module csr_window_ctrl (
    input clk_rst_n,
    input [5:0] csr_if_addr,
    input [63:0] csr_if_wdata,
    output reg [63:0] csr_if_rdata,
    input csr_if_we,
    input csr_if_re,
    input csr_if_valid,
    output reg csr_if_ready,
    output reg [15:0] timeout_limit_o,
    output reg [31:0] clamp_min_o,
    output reg [31:0] clamp_max_o,
    output reg [3:0] protocol_version_exp_o,
    output reg [3:0] request_type_mask_o,
    output reg diagnostic_reject_only_o,
    output reg fifo_enable_o,
    output reg [31:0] fallback_code_o,
    output reg [31:0] neutral_code_o,
    output reg [15:0] status_o
);
    reg [15:0] timeout_limit_r;
    reg [31:0] clamp_min_r;
    reg [31:0] clamp_max_r;
    reg [3:0] protocol_version_r;
    reg [3:0] request_type_mask_r;
    reg diagnostic_reject_only_r;
    reg fifo_enable_r;
    reg [31:0] fallback_code_r;
    reg [31:0] neutral_code_r;
    reg [15:0] status_r;

    always @(posedge clk_rst_n or negedge clk_rst_n) begin
        if (!clk_rst_n) begin
            timeout_limit_r <= 16'd256;
            clamp_min_r <= 32'h00000000;
            clamp_max_r <= 32'hFFFFFFFF;
            protocol_version_r <= 4'h1;
            request_type_mask_r <= 4'hF;
            diagnostic_reject_only_r <= 1'b0;
            fifo_enable_r <= 1'b0;
            fallback_code_r <= 32'h00000000;
            neutral_code_r <= 32'h00000000;
            status_r <= 16'h0000;
            csr_if_ready <= 1'b1;
            csr_if_rdata <= 64'h0000000000000000;
        end else begin
            csr_if_ready <= csr_if_valid;
            if (csr_if_valid && csr_if_we) begin
                case (csr_if_addr[3:0])
                    4'h0: timeout_limit_r <= csr_if_wdata[15:0];
                    4'h1: clamp_min_r <= csr_if_wdata[31:0];
                    4'h2: clamp_max_r <= csr_if_wdata[31:0];
                    4'h3: protocol_version_r <= csr_if_wdata[3:0];
                    4'h4: request_type_mask_r <= csr_if_wdata[3:0];
                    4'h5: diagnostic_reject_only_r <= csr_if_wdata[0];
                    4'h6: fifo_enable_r <= csr_if_wdata[0];
                    4'h7: fallback_code_r <= csr_if_wdata[31:0];
                    4'h8: neutral_code_r <= csr_if_wdata[31:0];
                    default: status_r <= status_r;
                endcase
            end
            status_r[0] <= status_r[0];
            csr_if_rdata <= 64'h0000000000000000;
            if (csr_if_valid && csr_if_re) begin
                case (csr_if_addr[3:0])
                    4'h0: csr_if_rdata <= {48'h000000000000, timeout_limit_r};
                    4'h1: csr_if_rdata <= {32'h00000000, clamp_min_r};
                    4'h2: csr_if_rdata <= {32'h00000000, clamp_max_r};
                    4'h3: csr_if_rdata <= {60'h000000000000000, protocol_version_r};
                    4'h4: csr_if_rdata <= {60'h000000000000000, request_type_mask_r};
                    4'h5: csr_if_rdata <= {63'h0000000000000000, diagnostic_reject_only_r};
                    4'h6: csr_if_rdata <= {63'h0000000000000000, fifo_enable_r};
                    4'h7: csr_if_rdata <= {32'h00000000, fallback_code_r};
                    4'h8: csr_if_rdata <= {32'h00000000, neutral_code_r};
                    4'h9: csr_if_rdata <= {48'h000000000000, status_r};
                    default: csr_if_rdata <= 64'h0000000000000000;
                endcase
            end
            timeout_limit_o <= timeout_limit_r;
            clamp_min_o <= clamp_min_r;
            clamp_max_o <= clamp_max_r;
            protocol_version_exp_o <= protocol_version_r;
            request_type_mask_o <= request_type_mask_r;
            diagnostic_reject_only_o <= diagnostic_reject_only_r;
            fifo_enable_o <= fifo_enable_r;
            fallback_code_o <= fallback_code_r;
            neutral_code_o <= neutral_code_r;
            status_o <= status_r;
        end
    end
endmodule
