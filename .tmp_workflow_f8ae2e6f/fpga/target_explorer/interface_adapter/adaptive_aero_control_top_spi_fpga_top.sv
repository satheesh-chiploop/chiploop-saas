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
  localparam integer INPUT_BITS = 129;
  localparam integer OUTPUT_BITS = 3;
  logic [INPUT_BITS-1:0] rx_shift, rx_active;
  logic [OUTPUT_BITS-1:0] tx_shift;
  logic [31:0] core_current_cycle_count;
  logic core_outstanding_valid;
  logic [31:0] core_outstanding_timestamp;
  logic [31:0] core_request_timeout_cycles;
  logic [31:0] core_freshness_limit_cycles;
  wire core_timeout_error;
  wire core_freshness_error;
  wire core_response_hold_timeout_error;
  assign core_current_cycle_count = rx_active[0 +: 32];
  assign core_outstanding_valid = rx_active[32 +: 1];
  assign core_outstanding_timestamp = rx_active[33 +: 32];
  assign core_request_timeout_cycles = rx_active[65 +: 32];
  assign core_freshness_limit_cycles = rx_active[97 +: 32];
  wire [OUTPUT_BITS-1:0] core_response = {core_timeout_error, core_freshness_error, core_response_hold_timeout_error};
  assign fault_indicator = 1'b0;
  always_ff @(posedge spi_sclk or posedge spi_cs_n or negedge reset_n) begin
    if (!reset_n) begin
      rx_shift <= '0; rx_active <= '0; tx_shift <= '0;
    end else if (spi_cs_n) begin
      rx_active <= rx_shift;
      tx_shift <= core_response;
    end else begin
      rx_shift <= {rx_shift[127:0], spi_mosi};
      tx_shift <= {tx_shift[1:0], 1'b0};
    end
  end
  always_comb spi_miso = tx_shift[OUTPUT_BITS-1];
  adaptive_aero_control_top u_core (
    .clk(clk),
    .rst_n(reset_n),
    .current_cycle_count(core_current_cycle_count),
    .outstanding_valid(core_outstanding_valid),
    .outstanding_timestamp(core_outstanding_timestamp),
    .request_timeout_cycles(core_request_timeout_cycles),
    .freshness_limit_cycles(core_freshness_limit_cycles),
    .timeout_error(core_timeout_error),
    .freshness_error(core_freshness_error),
    .response_hold_timeout_error(core_response_hold_timeout_error)
  );
endmodule
