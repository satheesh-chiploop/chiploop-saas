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
  localparam integer INPUT_BITS = 197;
  localparam integer OUTPUT_BITS = 204;
  localparam integer FRAME_BITS = 208;
  logic [FRAME_BITS-1:0] rx_shift;
  logic [INPUT_BITS-1:0] rx_active;
  logic [FRAME_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic [63:0] core_cfg_addr;
  logic [63:0] core_cfg_wdata;
  logic core_cfg_valid;
  logic core_cfg_write;
  logic core_model_req_ready;
  logic core_model_rsp_valid;
  logic [63:0] core_model_rsp_data;
  logic core_external_fault_i;
  wire [63:0] core_cfg_rdata;
  wire core_cfg_ready;
  wire core_model_req_valid;
  wire [63:0] core_model_req_data;
  wire core_model_rsp_ready;
  wire core_actuator_out_valid;
  wire [63:0] core_actuator_out_cmd;
  wire core_status_busy;
  wire core_status_accepted;
  wire core_status_rejected_stale;
  wire core_status_rejected_seq;
  wire core_status_timeout;
  wire core_status_fallback_active;
  wire core_status_clamped;
  wire core_status_fault_summary;
  assign core_cfg_addr = rx_active[0 +: 64];
  assign core_cfg_wdata = rx_active[64 +: 64];
  assign core_cfg_valid = rx_active[128 +: 1];
  assign core_cfg_write = rx_active[129 +: 1];
  assign core_model_req_ready = rx_active[130 +: 1];
  assign core_model_rsp_valid = rx_active[131 +: 1];
  assign core_model_rsp_data = rx_active[132 +: 64];
  assign core_external_fault_i = rx_active[196 +: 1];
  wire [OUTPUT_BITS-1:0] core_response = {core_cfg_rdata, core_cfg_ready, core_model_req_valid, core_model_req_data, core_model_rsp_ready, core_actuator_out_valid, core_actuator_out_cmd, core_status_busy, core_status_accepted, core_status_rejected_stale, core_status_rejected_seq, core_status_timeout, core_status_fallback_active, core_status_clamped, core_status_fault_summary};
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
      rx_shift <= {rx_shift[206:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[206:0], 1'b0};
      else tx_shift <= {tx_shift[206:0], 1'b0};
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
    .rst_n(reset_n),
    .cfg_addr(core_cfg_addr),
    .cfg_wdata(core_cfg_wdata),
    .cfg_rdata(core_cfg_rdata),
    .cfg_valid(core_cfg_valid),
    .cfg_write(core_cfg_write),
    .cfg_ready(core_cfg_ready),
    .model_req_valid(core_model_req_valid),
    .model_req_ready(core_model_req_ready),
    .model_req_data(core_model_req_data),
    .model_rsp_valid(core_model_rsp_valid),
    .model_rsp_ready(core_model_rsp_ready),
    .model_rsp_data(core_model_rsp_data),
    .external_fault_i(core_external_fault_i),
    .actuator_out_valid(core_actuator_out_valid),
    .actuator_out_cmd(core_actuator_out_cmd),
    .status_busy(core_status_busy),
    .status_accepted(core_status_accepted),
    .status_rejected_stale(core_status_rejected_stale),
    .status_rejected_seq(core_status_rejected_seq),
    .status_timeout(core_status_timeout),
    .status_fallback_active(core_status_fallback_active),
    .status_clamped(core_status_clamped),
    .status_fault_summary(core_status_fault_summary)
  );
endmodule
