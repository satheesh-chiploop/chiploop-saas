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
  localparam integer INPUT_BITS = 223;
  localparam integer OUTPUT_BITS = 229;
  localparam integer FRAME_BITS = 232;
  logic [FRAME_BITS-1:0] rx_shift;
  logic [INPUT_BITS-1:0] rx_active;
  logic [FRAME_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic [7:0] core_apb_ctrl_addr;
  logic [63:0] core_apb_ctrl_wdata;
  logic core_apb_ctrl_valid;
  logic core_apb_ctrl_write;
  logic core_host_req_stream_ready;
  logic core_host_resp_stream_valid;
  logic [127:0] core_host_resp_stream_data;
  logic [15:0] core_reg_fault_sticky;
  logic core_req_fifo_pop;
  logic core_req_fifo_full;
  logic core_req_fifo_empty;
  wire core_apb_ctrl_ready;
  wire [63:0] core_apb_ctrl_rdata;
  wire core_apb_ctrl_rvalid;
  wire core_host_req_stream_valid;
  wire [127:0] core_host_req_stream_data;
  wire core_host_resp_stream_ready;
  wire [31:0] core_actuator_cmd_bus;
  wire core_irq;
  assign core_apb_ctrl_addr = rx_active[0 +: 8];
  assign core_apb_ctrl_wdata = rx_active[8 +: 64];
  assign core_apb_ctrl_valid = rx_active[72 +: 1];
  assign core_apb_ctrl_write = rx_active[73 +: 1];
  assign core_host_req_stream_ready = rx_active[74 +: 1];
  assign core_host_resp_stream_valid = rx_active[75 +: 1];
  assign core_host_resp_stream_data = rx_active[76 +: 128];
  assign core_reg_fault_sticky = rx_active[204 +: 16];
  assign core_req_fifo_pop = rx_active[220 +: 1];
  assign core_req_fifo_full = rx_active[221 +: 1];
  assign core_req_fifo_empty = rx_active[222 +: 1];
  wire [OUTPUT_BITS-1:0] core_response = {core_apb_ctrl_ready, core_apb_ctrl_rdata, core_apb_ctrl_rvalid, core_host_req_stream_valid, core_host_req_stream_data, core_host_resp_stream_ready, core_actuator_cmd_bus, core_irq};
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
      rx_shift <= {rx_shift[230:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[230:0], 1'b0};
      else tx_shift <= {tx_shift[230:0], 1'b0};
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
  adaptive_aero_control_top u_core (
    .clk(clk),
    .reset_n(reset_n),
    .apb_ctrl_addr(core_apb_ctrl_addr),
    .apb_ctrl_wdata(core_apb_ctrl_wdata),
    .apb_ctrl_valid(core_apb_ctrl_valid),
    .apb_ctrl_write(core_apb_ctrl_write),
    .apb_ctrl_ready(core_apb_ctrl_ready),
    .apb_ctrl_rdata(core_apb_ctrl_rdata),
    .apb_ctrl_rvalid(core_apb_ctrl_rvalid),
    .host_req_stream_valid(core_host_req_stream_valid),
    .host_req_stream_data(core_host_req_stream_data),
    .host_req_stream_ready(core_host_req_stream_ready),
    .host_resp_stream_valid(core_host_resp_stream_valid),
    .host_resp_stream_data(core_host_resp_stream_data),
    .host_resp_stream_ready(core_host_resp_stream_ready),
    .actuator_cmd_bus(core_actuator_cmd_bus),
    .irq(core_irq),
    .reg_fault_sticky(core_reg_fault_sticky),
    .req_fifo_pop(core_req_fifo_pop),
    .req_fifo_full(core_req_fifo_full),
    .req_fifo_empty(core_req_fifo_empty)
  );
endmodule
