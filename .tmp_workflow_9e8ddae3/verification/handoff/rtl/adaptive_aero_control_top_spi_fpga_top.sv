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
  localparam integer INPUT_BITS = 196;
  localparam integer OUTPUT_BITS = 241;
  logic [INPUT_BITS-1:0] rx_shift, rx_active;
  logic [OUTPUT_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic [7:0] core_mmio_addr;
  logic [31:0] core_mmio_wdata;
  logic core_mmio_valid;
  logic core_mmio_write;
  logic core_req_ready;
  logic core_resp_valid;
  logic [127:0] core_resp_data;
  logic [15:0] core_response_seq_probe;
  logic [7:0] core_response_status_flags_probe;
  wire [31:0] core_mmio_rdata;
  wire core_mmio_ready;
  wire core_req_valid;
  wire [127:0] core_req_data;
  wire core_resp_ready;
  wire core_actuator_valid;
  wire [15:0] core_actuator_cmd;
  wire core_safe_fallback_active;
  wire core_timeout_expired;
  wire [15:0] core_current_cycle_age;
  wire core_bram_csb;
  wire core_bram_web;
  wire [8:0] core_bram_addr;
  wire [31:0] core_bram_din;
  assign core_mmio_addr = rx_active[0 +: 8];
  assign core_mmio_wdata = rx_active[8 +: 32];
  assign core_mmio_valid = rx_active[40 +: 1];
  assign core_mmio_write = rx_active[41 +: 1];
  assign core_req_ready = rx_active[42 +: 1];
  assign core_resp_valid = rx_active[43 +: 1];
  assign core_resp_data = rx_active[44 +: 128];
  assign core_response_seq_probe = rx_active[172 +: 16];
  assign core_response_status_flags_probe = rx_active[188 +: 8];
  wire [OUTPUT_BITS-1:0] core_response = {core_mmio_rdata, core_mmio_ready, core_req_valid, core_req_data, core_resp_ready, core_actuator_valid, core_actuator_cmd, core_safe_fallback_active, core_timeout_expired, core_current_cycle_age, core_bram_csb, core_bram_web, core_bram_addr, core_bram_din};
  assign fault_indicator = 1'b0;
  // Chip select asynchronously clears only the frame-state bit. Data
  // registers use SPI clock alone, which is legal in ECP5 fabric.
  always_ff @(posedge spi_sclk or posedge spi_cs_n) begin
    if (spi_cs_n) spi_active <= 1'b0;
    else spi_active <= 1'b1;
  end
  always_ff @(posedge spi_sclk) begin
    if (!spi_cs_n) begin
      rx_shift <= {rx_shift[194:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[239:0], 1'b0};
      else tx_shift <= {tx_shift[239:0], 1'b0};
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
    .mmio_valid(core_mmio_valid),
    .mmio_write(core_mmio_write),
    .mmio_rdata(core_mmio_rdata),
    .mmio_ready(core_mmio_ready),
    .req_valid(core_req_valid),
    .req_ready(core_req_ready),
    .req_data(core_req_data),
    .resp_valid(core_resp_valid),
    .resp_ready(core_resp_ready),
    .resp_data(core_resp_data),
    .actuator_valid(core_actuator_valid),
    .actuator_cmd(core_actuator_cmd),
    .safe_fallback_active(core_safe_fallback_active),
    .response_seq_probe(core_response_seq_probe),
    .response_status_flags_probe(core_response_status_flags_probe),
    .timeout_expired(core_timeout_expired),
    .current_cycle_age(core_current_cycle_age),
    .bram_csb(core_bram_csb),
    .bram_web(core_bram_web),
    .bram_addr(core_bram_addr),
    .bram_din(core_bram_din)
  );
endmodule
