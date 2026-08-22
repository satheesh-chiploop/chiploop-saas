// Auto-generated FPGA-only serialized transport shell.
// The verified core RTL remains unchanged; ASIC flows continue to use the core top.
module adaptive_aero_control_top_spi_fpga_top_spi_fpga_top (
  input  logic clk,
  input  logic reset_n,
  input  logic spi_sclk,
  input  logic spi_cs_n,
  input  logic spi_mosi,
  output logic spi_miso,
  output logic fault_indicator
);
  localparam integer INPUT_BITS = 3;
  localparam integer OUTPUT_BITS = 2;
  localparam integer FRAME_BITS = 8;
  logic [FRAME_BITS-1:0] rx_shift;
  logic [INPUT_BITS-1:0] rx_active;
  logic [FRAME_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic core_spi_sclk;
  logic core_spi_cs_n;
  logic core_spi_mosi;
  wire core_spi_miso;
  wire core_fault_indicator;
  assign core_spi_sclk = rx_active[0 +: 1];
  assign core_spi_cs_n = rx_active[1 +: 1];
  assign core_spi_mosi = rx_active[2 +: 1];
  wire [OUTPUT_BITS-1:0] core_response = {core_spi_miso, core_fault_indicator};
  wire [FRAME_BITS-1:0] framed_response = {core_response, {(FRAME_BITS-OUTPUT_BITS){1'b0}}};
  assign fault_indicator = 1'b0;
  // Chip select asynchronously clears only the frame-state bit. Data
  // registers use SPI clock alone, which is legal in ECP5 fabric.
  always_ff @(posedge spi_sclk or posedge spi_cs_n) begin
    if (spi_cs_n) spi_active <= 1'b0;
    else spi_active <= 1'b1;
  end
  always_ff @(posedge spi_sclk) begin
    if (!spi_cs_n) begin
      rx_shift <= {rx_shift[6:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[6:0], 1'b0};
      else tx_shift <= {tx_shift[6:0], 1'b0};
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
      if (spi_cs_sync && !spi_cs_prev) begin
        rx_active <= rx_shift[INPUT_BITS-1:0];
        // Bundled-data CDC: capture once, then hold this mailbox stable
        // until the next completed frame. The host observes response N in frame N+2.
        tx_snapshot <= framed_response;
      end
    end
  end
  // Release the shared MISO/SD net whenever chip select is inactive.
  always_comb spi_miso = !spi_cs_n ? (spi_active ? tx_shift[FRAME_BITS-1] : tx_snapshot[FRAME_BITS-1]) : 1'bz;
  adaptive_aero_control_top_spi_fpga_top u_core (
    .clk(clk),
    .reset_n(reset_n),
    .spi_sclk(core_spi_sclk),
    .spi_cs_n(core_spi_cs_n),
    .spi_mosi(core_spi_mosi),
    .spi_miso(core_spi_miso),
    .fault_indicator(core_fault_indicator)
  );
endmodule
