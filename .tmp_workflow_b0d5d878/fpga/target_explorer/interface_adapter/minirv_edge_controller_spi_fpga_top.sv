// Auto-generated FPGA-only serialized transport shell.
// The verified core RTL remains unchanged; ASIC flows continue to use the core top.
module minirv_edge_controller_spi_fpga_top (
  input  logic clk,
  input  logic reset_n,
  input  logic spi_sclk,
  input  logic spi_cs_n,
  input  logic spi_mosi,
  output logic spi_miso,
  output logic fault_indicator
);
  localparam integer INPUT_BITS = 42;
  localparam integer OUTPUT_BITS = 38;
  logic [INPUT_BITS-1:0] rx_shift, rx_active;
  logic [OUTPUT_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic [3:0] core_debug_addr_a;
  logic [3:0] core_debug_addr_b;
  logic [31:0] core_sensor_data;
  logic core_sensor_valid;
  logic core_uart_rx;
  wire core_uart_tx;
  wire [3:0] core_pwm_out;
  wire [31:0] core_debug_data;
  wire core_interrupt;
  assign core_debug_addr_a = rx_active[0 +: 4];
  assign core_debug_addr_b = rx_active[4 +: 4];
  assign core_sensor_data = rx_active[8 +: 32];
  assign core_sensor_valid = rx_active[40 +: 1];
  assign core_uart_rx = rx_active[41 +: 1];
  wire [OUTPUT_BITS-1:0] core_response = {core_uart_tx, core_pwm_out, core_debug_data, core_interrupt};
  assign fault_indicator = 1'b0;
  // Chip select asynchronously clears only the frame-state bit. Data
  // registers use SPI clock alone, which is legal in ECP5 fabric.
  always_ff @(posedge spi_sclk or posedge spi_cs_n) begin
    if (spi_cs_n) spi_active <= 1'b0;
    else spi_active <= 1'b1;
  end
  always_ff @(posedge spi_sclk) begin
    if (!spi_cs_n) begin
      rx_shift <= {rx_shift[40:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[36:0], 1'b0};
      else tx_shift <= {tx_shift[36:0], 1'b0};
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
  minirv_edge_controller u_core (
    .clk(clk),
    .reset_n(reset_n),
    .debug_addr_a(core_debug_addr_a),
    .debug_addr_b(core_debug_addr_b),
    .sensor_data(core_sensor_data),
    .sensor_valid(core_sensor_valid),
    .uart_rx(core_uart_rx),
    .uart_tx(core_uart_tx),
    .pwm_out(core_pwm_out),
    .debug_data(core_debug_data),
    .interrupt(core_interrupt)
  );
endmodule
