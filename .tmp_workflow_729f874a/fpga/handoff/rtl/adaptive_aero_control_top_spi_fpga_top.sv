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
  localparam integer INPUT_BITS = 109;
  localparam integer OUTPUT_BITS = 150;
  localparam integer FRAME_BITS = 152;
  logic [FRAME_BITS-1:0] rx_shift;
  logic [INPUT_BITS-1:0] rx_active;
  logic [FRAME_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic [7:0] core_mmio_addr;
  logic [31:0] core_mmio_wdata;
  logic core_mmio_valid;
  logic core_mmio_write;
  logic core_model_req_ready;
  logic core_model_rsp_valid;
  logic [63:0] core_model_rsp_data;
  logic core_actuator_cmd_ready;
  wire [31:0] core_mmio_rdata;
  wire core_mmio_ready;
  wire core_model_req_valid;
  wire [63:0] core_model_req_data;
  wire core_model_rsp_ready;
  wire core_actuator_cmd_valid;
  wire [15:0] core_actuator_cmd_data;
  wire core_fault_latched;
  wire core_status_valid;
  wire [31:0] core_status_data;
  assign core_mmio_addr = rx_active[0 +: 8];
  assign core_mmio_wdata = rx_active[8 +: 32];
  assign core_mmio_valid = rx_active[40 +: 1];
  assign core_mmio_write = rx_active[41 +: 1];
  assign core_model_req_ready = rx_active[42 +: 1];
  assign core_model_rsp_valid = rx_active[43 +: 1];
  assign core_model_rsp_data = rx_active[44 +: 64];
  assign core_actuator_cmd_ready = rx_active[108 +: 1];
  wire [OUTPUT_BITS-1:0] core_response = {core_mmio_rdata, core_mmio_ready, core_model_req_valid, core_model_req_data, core_model_rsp_ready, core_actuator_cmd_valid, core_actuator_cmd_data, core_fault_latched, core_status_valid, core_status_data};
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
      rx_shift <= {rx_shift[150:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[150:0], 1'b0};
      else tx_shift <= {tx_shift[150:0], 1'b0};
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
  // MISO is a dedicated top-level output. Drive a defined idle value
  // instead of inferring an internal tri-state cell, which is not a
  // portable fabric primitive and breaks mapped equivalence on targets
  // such as ECP5. Board-specific shared-data buses require an explicit
  // vendor I/O-buffer wrapper outside this transport shell.
  always_comb spi_miso = !spi_cs_n ? (spi_active ? tx_shift[FRAME_BITS-1] : tx_snapshot[FRAME_BITS-1]) : 1'b0;
  adaptive_aero_control_top u_core (
    .clk(clk),
    .reset_n(reset_n),
    .mmio_addr(core_mmio_addr),
    .mmio_wdata(core_mmio_wdata),
    .mmio_valid(core_mmio_valid),
    .mmio_write(core_mmio_write),
    .mmio_rdata(core_mmio_rdata),
    .mmio_ready(core_mmio_ready),
    .model_req_valid(core_model_req_valid),
    .model_req_data(core_model_req_data),
    .model_req_ready(core_model_req_ready),
    .model_rsp_valid(core_model_rsp_valid),
    .model_rsp_data(core_model_rsp_data),
    .model_rsp_ready(core_model_rsp_ready),
    .actuator_cmd_valid(core_actuator_cmd_valid),
    .actuator_cmd_data(core_actuator_cmd_data),
    .actuator_cmd_ready(core_actuator_cmd_ready),
    .fault_latched(core_fault_latched),
    .status_valid(core_status_valid),
    .status_data(core_status_data)
  );
endmodule
