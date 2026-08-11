// Auto-generated FPGA-only serialized transport shell.
// The verified core RTL remains unchanged; ASIC flows continue to use the core top.
module adaptive_aero_control_top_spi_fpga_top (
  input  logic clk,
  input  logic reset_n,
  input  logic spi_sclk,
  input  logic spi_cs_n,
  input  logic spi_mosi,
  output logic spi_miso,
  output logic fault_indicator
);
  localparam integer INPUT_BITS = 203;
  localparam integer OUTPUT_BITS = 227;
  logic [INPUT_BITS-1:0] rx_shift, rx_active;
  logic [OUTPUT_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic core_cfg_wr_en;
  logic core_cfg_rd_en;
  logic [5:0] core_cfg_addr;
  logic [63:0] core_cfg_wdata;
  logic core_req_stream_ready;
  logic core_rsp_stream_valid;
  logic [127:0] core_rsp_stream_data;
  logic core_actuator_cmd_ready;
  wire [63:0] core_cfg_rdata;
  wire core_req_stream_valid;
  wire [127:0] core_req_stream_data;
  wire core_rsp_stream_ready;
  wire core_actuator_cmd_valid;
  wire [31:0] core_actuator_cmd_data;
  assign core_cfg_wr_en = rx_active[0 +: 1];
  assign core_cfg_rd_en = rx_active[1 +: 1];
  assign core_cfg_addr = rx_active[2 +: 6];
  assign core_cfg_wdata = rx_active[8 +: 64];
  assign core_req_stream_ready = rx_active[72 +: 1];
  assign core_rsp_stream_valid = rx_active[73 +: 1];
  assign core_rsp_stream_data = rx_active[74 +: 128];
  assign core_actuator_cmd_ready = rx_active[202 +: 1];
  wire [OUTPUT_BITS-1:0] core_response = {core_cfg_rdata, core_req_stream_valid, core_req_stream_data, core_rsp_stream_ready, core_actuator_cmd_valid, core_actuator_cmd_data};
  assign fault_indicator = 1'b0;
  // Chip select asynchronously clears only the frame-state bit. Data
  // registers use SPI clock alone, which is legal in ECP5 fabric.
  always_ff @(posedge spi_sclk or posedge spi_cs_n) begin
    if (spi_cs_n) spi_active <= 1'b0;
    else spi_active <= 1'b1;
  end
  always_ff @(posedge spi_sclk) begin
    if (!spi_cs_n) begin
      rx_shift <= {rx_shift[201:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[225:0], 1'b0};
      else tx_shift <= {tx_shift[225:0], 1'b0};
    end
  end
  // Synchronize frame completion into the core clock domain. The host
  // keeps MOSI stable around CS rising as required by the protocol.
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      spi_cs_meta <= 1'b1; spi_cs_sync <= 1'b1; spi_cs_prev <= 1'b1;
      rx_active <= '0; tx_snapshot <= '0;
    end else begin
      spi_cs_meta <= spi_cs_n; spi_cs_sync <= spi_cs_meta; spi_cs_prev <= spi_cs_sync;
      if (spi_cs_sync && !spi_cs_prev) rx_active <= rx_shift;
      tx_snapshot <= core_response;
    end
  end
  always_comb spi_miso = spi_active ? tx_shift[OUTPUT_BITS-1] : tx_snapshot[OUTPUT_BITS-1];
  adaptive_aero_control_top u_core (
    .clk(clk),
    .rst_n(reset_n),
    .cfg_wr_en(core_cfg_wr_en),
    .cfg_rd_en(core_cfg_rd_en),
    .cfg_addr(core_cfg_addr),
    .cfg_wdata(core_cfg_wdata),
    .cfg_rdata(core_cfg_rdata),
    .req_stream_valid(core_req_stream_valid),
    .req_stream_ready(core_req_stream_ready),
    .req_stream_data(core_req_stream_data),
    .rsp_stream_valid(core_rsp_stream_valid),
    .rsp_stream_ready(core_rsp_stream_ready),
    .rsp_stream_data(core_rsp_stream_data),
    .actuator_cmd_valid(core_actuator_cmd_valid),
    .actuator_cmd_ready(core_actuator_cmd_ready),
    .actuator_cmd_data(core_actuator_cmd_data)
  );
endmodule
