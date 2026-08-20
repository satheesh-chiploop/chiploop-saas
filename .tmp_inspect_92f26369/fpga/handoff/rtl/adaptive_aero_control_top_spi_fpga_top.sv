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
  localparam integer INPUT_BITS = 177;
  localparam integer OUTPUT_BITS = 198;
  logic [INPUT_BITS-1:0] rx_shift, rx_active;
  logic [OUTPUT_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic [7:0] core_wb_adr_i;
  logic [31:0] core_wb_dat_i;
  logic core_wb_we_i;
  logic core_wb_stb_i;
  logic core_wb_cyc_i;
  logic [3:0] core_wb_sel_i;
  logic core_req_ready_i;
  logic core_rsp_valid_i;
  logic [127:0] core_rsp_payload_i;
  wire [31:0] core_wb_dat_o;
  wire core_wb_ack_o;
  wire core_wb_err_o;
  wire core_req_valid_o;
  wire [127:0] core_req_payload_o;
  wire core_rsp_ready_o;
  wire [31:0] core_actuator_cmd_o;
  wire core_fault_o;
  wire core_irq_o;
  assign core_wb_adr_i = rx_active[0 +: 8];
  assign core_wb_dat_i = rx_active[8 +: 32];
  assign core_wb_we_i = rx_active[40 +: 1];
  assign core_wb_stb_i = rx_active[41 +: 1];
  assign core_wb_cyc_i = rx_active[42 +: 1];
  assign core_wb_sel_i = rx_active[43 +: 4];
  assign core_req_ready_i = rx_active[47 +: 1];
  assign core_rsp_valid_i = rx_active[48 +: 1];
  assign core_rsp_payload_i = rx_active[49 +: 128];
  wire [OUTPUT_BITS-1:0] core_response = {core_wb_dat_o, core_wb_ack_o, core_wb_err_o, core_req_valid_o, core_req_payload_o, core_rsp_ready_o, core_actuator_cmd_o, core_fault_o, core_irq_o};
  assign fault_indicator = 1'b0;
  // Chip select asynchronously clears only the frame-state bit. Data
  // registers use SPI clock alone, which is legal in ECP5 fabric.
  always_ff @(posedge spi_sclk or posedge spi_cs_n) begin
    if (spi_cs_n) spi_active <= 1'b0;
    else spi_active <= 1'b1;
  end
  always_ff @(posedge spi_sclk) begin
    if (!spi_cs_n) begin
      rx_shift <= {rx_shift[175:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[196:0], 1'b0};
      else tx_shift <= {tx_shift[196:0], 1'b0};
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
    .wb_adr_i(core_wb_adr_i),
    .wb_dat_i(core_wb_dat_i),
    .wb_dat_o(core_wb_dat_o),
    .wb_we_i(core_wb_we_i),
    .wb_stb_i(core_wb_stb_i),
    .wb_cyc_i(core_wb_cyc_i),
    .wb_ack_o(core_wb_ack_o),
    .wb_err_o(core_wb_err_o),
    .wb_sel_i(core_wb_sel_i),
    .req_valid_o(core_req_valid_o),
    .req_ready_i(core_req_ready_i),
    .req_payload_o(core_req_payload_o),
    .rsp_valid_i(core_rsp_valid_i),
    .rsp_ready_o(core_rsp_ready_o),
    .rsp_payload_i(core_rsp_payload_i),
    .actuator_cmd_o(core_actuator_cmd_o),
    .fault_o(core_fault_o),
    .irq_o(core_irq_o)
  );
endmodule
