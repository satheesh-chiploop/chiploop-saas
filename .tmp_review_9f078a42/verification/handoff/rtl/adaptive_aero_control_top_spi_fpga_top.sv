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
  localparam integer INPUT_BITS = 136;
  localparam integer OUTPUT_BITS = 167;
  logic [INPUT_BITS-1:0] rx_shift, rx_active;
  logic [OUTPUT_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic [3:0] core_mmio_addr;
  logic [63:0] core_mmio_wdata;
  logic core_mmio_we;
  logic core_mmio_re;
  logic core_req_ready;
  logic core_rsp_valid;
  logic [63:0] core_rsp_data;
  wire [63:0] core_mmio_rdata;
  wire core_mmio_ready;
  wire core_mmio_error;
  wire core_req_valid;
  wire [63:0] core_req_data;
  wire core_rsp_ready;
  wire core_act_cmd_valid;
  wire core_act_cmd_fault;
  wire [31:0] core_act_cmd_data;
  wire core_irq;
  assign core_mmio_addr = rx_active[0 +: 4];
  assign core_mmio_wdata = rx_active[4 +: 64];
  assign core_mmio_we = rx_active[68 +: 1];
  assign core_mmio_re = rx_active[69 +: 1];
  assign core_req_ready = rx_active[70 +: 1];
  assign core_rsp_valid = rx_active[71 +: 1];
  assign core_rsp_data = rx_active[72 +: 64];
  wire [OUTPUT_BITS-1:0] core_response = {core_mmio_rdata, core_mmio_ready, core_mmio_error, core_req_valid, core_req_data, core_rsp_ready, core_act_cmd_valid, core_act_cmd_fault, core_act_cmd_data, core_irq};
  assign fault_indicator = 1'b0;
  // Chip select asynchronously clears only the frame-state bit. Data
  // registers use SPI clock alone, which is legal in ECP5 fabric.
  always_ff @(posedge spi_sclk or posedge spi_cs_n) begin
    if (spi_cs_n) spi_active <= 1'b0;
    else spi_active <= 1'b1;
  end
  always_ff @(posedge spi_sclk) begin
    if (!spi_cs_n) begin
      rx_shift <= {rx_shift[134:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[165:0], 1'b0};
      else tx_shift <= {tx_shift[165:0], 1'b0};
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
    .reset_n(reset_n),
    .mmio_addr(core_mmio_addr),
    .mmio_wdata(core_mmio_wdata),
    .mmio_we(core_mmio_we),
    .mmio_re(core_mmio_re),
    .mmio_rdata(core_mmio_rdata),
    .mmio_ready(core_mmio_ready),
    .mmio_error(core_mmio_error),
    .req_valid(core_req_valid),
    .req_ready(core_req_ready),
    .req_data(core_req_data),
    .rsp_valid(core_rsp_valid),
    .rsp_ready(core_rsp_ready),
    .rsp_data(core_rsp_data),
    .act_cmd_valid(core_act_cmd_valid),
    .act_cmd_fault(core_act_cmd_fault),
    .act_cmd_data(core_act_cmd_data),
    .irq(core_irq)
  );
endmodule
