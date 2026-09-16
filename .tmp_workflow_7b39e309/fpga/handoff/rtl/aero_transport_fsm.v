module aero_transport_fsm(
    clk,
    reset_n,
    spi_cs_n,
    spi_sclk,
    spi_mosi,
    spi_miso,
    host_cmd_valid,
    host_cmd_opcode,
    host_cmd_data,
    host_rsp_ready,
    host_rsp_valid,
    host_rsp_data,
    model_req_valid,
    model_req_data,
    model_req_ready,
    fault_latched,
    status_valid,
    status_code
);
input clk;
input reset_n;
input spi_cs_n;
input spi_sclk;
input spi_mosi;
output spi_miso;
input host_cmd_valid;
input [7:0] host_cmd_opcode;
input [31:0] host_cmd_data;
input host_rsp_ready;
output reg host_rsp_valid;
output reg [31:0] host_rsp_data;
output reg model_req_valid;
output reg [31:0] model_req_data;
input model_req_ready;
input fault_latched;
input status_valid;
input [7:0] status_code;
reg [7:0] spi_shift;
reg [2:0] spi_bit_cnt;
reg spi_sclk_d;
reg spi_mosi_sync;
reg [7:0] rsp_byte_sel;
reg [1:0] rsp_phase;

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        spi_shift <= 8'h00;
        spi_bit_cnt <= 3'b000;
        spi_sclk_d <= 1'b0;
        spi_mosi_sync <= 1'b0;
        rsp_byte_sel <= 8'h00;
        rsp_phase <= 2'b00;
        host_rsp_valid <= 1'b0;
        host_rsp_data <= 32'h00000000;
        model_req_valid <= 1'b0;
        model_req_data <= 32'h00000000;
    end else begin
        spi_sclk_d <= spi_sclk;
        spi_mosi_sync <= spi_mosi;
        if (!spi_cs_n && host_cmd_valid) begin
            model_req_valid <= 1'b1;
            model_req_data <= {host_cmd_opcode, host_cmd_data[23:0]};
            rsp_byte_sel <= host_cmd_opcode;
            rsp_phase <= 2'b01;
            host_rsp_valid <= 1'b1;
            host_rsp_data <= {status_code, 8'h00, host_cmd_opcode, spi_shift};
        end else if (model_req_valid && model_req_ready) begin
            model_req_valid <= 1'b0;
            rsp_phase <= 2'b10;
            host_rsp_valid <= status_valid | host_rsp_ready;
            host_rsp_data <= {status_code, 16'h0000, rsp_byte_sel};
        end else if (host_rsp_ready) begin
            host_rsp_valid <= 1'b0;
            rsp_phase <= 2'b00;
        end
        if (spi_cs_n) begin
            spi_shift <= 8'h00;
            spi_bit_cnt <= 3'b000;
        end else if (spi_sclk_d ^ spi_sclk) begin
            spi_shift <= {spi_shift[6:0], spi_mosi_sync};
            spi_bit_cnt <= spi_bit_cnt + 3'b001;
        end
        if (fault_latched) begin
            host_rsp_valid <= 1'b1;
            host_rsp_data <= {status_code, 8'hFA, 8'h00, 8'h01};
        end
    end
end

assign spi_miso = spi_shift[7] ^ fault_latched;

endmodule
