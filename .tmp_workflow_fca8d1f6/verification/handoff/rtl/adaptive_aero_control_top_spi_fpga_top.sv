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
  localparam integer INPUT_BITS = 110;
  localparam integer OUTPUT_BITS = 118;
  localparam integer FRAME_BITS = 120;
  logic [FRAME_BITS-1:0] rx_shift;
  logic [INPUT_BITS-1:0] rx_active;
  logic [FRAME_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic core_reg_cs_n;
  logic core_reg_valid;
  logic core_reg_we;
  logic core_reg_re;
  logic [7:0] core_reg_addr;
  logic [31:0] core_reg_wdata;
  logic core_req_ready;
  logic core_rsp_valid;
  logic [63:0] core_rsp_data;
  wire [31:0] core_reg_rdata;
  wire core_reg_ready;
  wire core_reg_status;
  wire core_req_valid;
  wire [63:0] core_req_data;
  wire core_rsp_ready;
  wire core_act_cmd_valid;
  wire [15:0] core_act_cmd;
  wire core_fault_irq;
  assign core_reg_cs_n = rx_active[0 +: 1];
  assign core_reg_valid = rx_active[1 +: 1];
  assign core_reg_we = rx_active[2 +: 1];
  assign core_reg_re = rx_active[3 +: 1];
  assign core_reg_addr = rx_active[4 +: 8];
  assign core_reg_wdata = rx_active[12 +: 32];
  assign core_req_ready = rx_active[44 +: 1];
  assign core_rsp_valid = rx_active[45 +: 1];
  assign core_rsp_data = rx_active[46 +: 64];
  wire [OUTPUT_BITS-1:0] core_response = {core_reg_rdata, core_reg_ready, core_reg_status, core_req_valid, core_req_data, core_rsp_ready, core_act_cmd_valid, core_act_cmd, core_fault_irq};
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
      rx_shift <= {rx_shift[118:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[118:0], 1'b0};
      else tx_shift <= {tx_shift[118:0], 1'b0};
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
    .reg_cs_n(core_reg_cs_n),
    .reg_valid(core_reg_valid),
    .reg_we(core_reg_we),
    .reg_re(core_reg_re),
    .reg_addr(core_reg_addr),
    .reg_wdata(core_reg_wdata),
    .reg_rdata(core_reg_rdata),
    .reg_ready(core_reg_ready),
    .reg_status(core_reg_status),
    .req_valid(core_req_valid),
    .req_ready(core_req_ready),
    .req_data(core_req_data),
    .rsp_valid(core_rsp_valid),
    .rsp_ready(core_rsp_ready),
    .rsp_data(core_rsp_data),
    .act_cmd_valid(core_act_cmd_valid),
    .act_cmd(core_act_cmd),
    .fault_irq(core_fault_irq)
  );
endmodule
