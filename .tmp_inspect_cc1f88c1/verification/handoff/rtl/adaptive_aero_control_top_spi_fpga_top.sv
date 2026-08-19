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
  localparam integer INPUT_BITS = 143;
  localparam integer OUTPUT_BITS = 135;
  logic [INPUT_BITS-1:0] rx_shift, rx_active;
  logic [OUTPUT_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic [31:0] core_wb_adr_i;
  logic [31:0] core_wb_dat_i;
  logic core_wb_we_i;
  logic core_wb_cyc_i;
  logic core_wb_stb_i;
  logic [3:0] core_wb_sel_i;
  logic [2:0] core_wb_cti_i;
  logic [1:0] core_wb_bte_i;
  logic core_model_req_ready;
  logic core_model_rsp_valid;
  logic [63:0] core_model_rsp_data;
  logic core_actuator_cmd_ready;
  wire [31:0] core_wb_dat_o;
  wire core_wb_ack_o;
  wire core_wb_stall_o;
  wire core_wb_err_o;
  wire core_irq_o;
  wire core_model_req_valid;
  wire [63:0] core_model_req_data;
  wire core_model_rsp_ready;
  wire core_actuator_cmd_valid;
  wire [31:0] core_actuator_cmd_data;
  assign core_wb_adr_i = rx_active[0 +: 32];
  assign core_wb_dat_i = rx_active[32 +: 32];
  assign core_wb_we_i = rx_active[64 +: 1];
  assign core_wb_cyc_i = rx_active[65 +: 1];
  assign core_wb_stb_i = rx_active[66 +: 1];
  assign core_wb_sel_i = rx_active[67 +: 4];
  assign core_wb_cti_i = rx_active[71 +: 3];
  assign core_wb_bte_i = rx_active[74 +: 2];
  assign core_model_req_ready = rx_active[76 +: 1];
  assign core_model_rsp_valid = rx_active[77 +: 1];
  assign core_model_rsp_data = rx_active[78 +: 64];
  assign core_actuator_cmd_ready = rx_active[142 +: 1];
  wire [OUTPUT_BITS-1:0] core_response = {core_wb_dat_o, core_wb_ack_o, core_wb_stall_o, core_wb_err_o, core_irq_o, core_model_req_valid, core_model_req_data, core_model_rsp_ready, core_actuator_cmd_valid, core_actuator_cmd_data};
  assign fault_indicator = 1'b0;
  // Chip select asynchronously clears only the frame-state bit. Data
  // registers use SPI clock alone, which is legal in ECP5 fabric.
  always_ff @(posedge spi_sclk or posedge spi_cs_n) begin
    if (spi_cs_n) spi_active <= 1'b0;
    else spi_active <= 1'b1;
  end
  always_ff @(posedge spi_sclk) begin
    if (!spi_cs_n) begin
      rx_shift <= {rx_shift[141:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[133:0], 1'b0};
      else tx_shift <= {tx_shift[133:0], 1'b0};
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
    .wb_cyc_i(core_wb_cyc_i),
    .wb_stb_i(core_wb_stb_i),
    .wb_ack_o(core_wb_ack_o),
    .wb_stall_o(core_wb_stall_o),
    .wb_err_o(core_wb_err_o),
    .wb_sel_i(core_wb_sel_i),
    .wb_cti_i(core_wb_cti_i),
    .wb_bte_i(core_wb_bte_i),
    .irq_o(core_irq_o),
    .model_req_valid(core_model_req_valid),
    .model_req_data(core_model_req_data),
    .model_req_ready(core_model_req_ready),
    .model_rsp_valid(core_model_rsp_valid),
    .model_rsp_data(core_model_rsp_data),
    .model_rsp_ready(core_model_rsp_ready),
    .actuator_cmd_valid(core_actuator_cmd_valid),
    .actuator_cmd_ready(core_actuator_cmd_ready),
    .actuator_cmd_data(core_actuator_cmd_data)
  );
endmodule
