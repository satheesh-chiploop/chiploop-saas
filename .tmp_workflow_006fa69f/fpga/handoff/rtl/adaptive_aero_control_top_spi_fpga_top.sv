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
  localparam integer INPUT_BITS = 199;
  localparam integer OUTPUT_BITS = 275;
  logic [INPUT_BITS-1:0] rx_shift, rx_active;
  logic [OUTPUT_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic [3:0] core_reg_addr;
  logic [63:0] core_reg_wdata;
  logic core_model_req_ready;
  logic core_model_rsp_valid;
  logic [127:0] core_model_rsp_data;
  logic core_actuator_cmd_ready;
  wire [63:0] core_reg_rdata;
  wire core_model_req_valid;
  wire [127:0] core_model_req_data;
  wire core_model_rsp_ready;
  wire core_actuator_cmd_valid;
  wire [63:0] core_actuator_cmd_data;
  wire [7:0] core_fault_summary;
  wire [7:0] core_heartbeat_status;
  assign core_reg_addr = rx_active[0 +: 4];
  assign core_reg_wdata = rx_active[4 +: 64];
  assign core_model_req_ready = rx_active[68 +: 1];
  assign core_model_rsp_valid = rx_active[69 +: 1];
  assign core_model_rsp_data = rx_active[70 +: 128];
  assign core_actuator_cmd_ready = rx_active[198 +: 1];
  wire [OUTPUT_BITS-1:0] core_response = {core_reg_rdata, core_model_req_valid, core_model_req_data, core_model_rsp_ready, core_actuator_cmd_valid, core_actuator_cmd_data, core_fault_summary, core_heartbeat_status};
  assign fault_indicator = 1'b0;
  // Chip select asynchronously clears only the frame-state bit. Data
  // registers use SPI clock alone, which is legal in ECP5 fabric.
  always_ff @(posedge spi_sclk or posedge spi_cs_n) begin
    if (spi_cs_n) spi_active <= 1'b0;
    else spi_active <= 1'b1;
  end
  always_ff @(posedge spi_sclk) begin
    if (!spi_cs_n) begin
      rx_shift <= {rx_shift[197:0], spi_mosi};
      if (!spi_active) tx_shift <= {tx_snapshot[273:0], 1'b0};
      else tx_shift <= {tx_shift[273:0], 1'b0};
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
    .reset(~reset_n),
    .reg_addr(core_reg_addr),
    .reg_wdata(core_reg_wdata),
    .reg_rdata(core_reg_rdata),
    .model_req_valid(core_model_req_valid),
    .model_req_ready(core_model_req_ready),
    .model_req_data(core_model_req_data),
    .model_rsp_valid(core_model_rsp_valid),
    .model_rsp_ready(core_model_rsp_ready),
    .model_rsp_data(core_model_rsp_data),
    .actuator_cmd_valid(core_actuator_cmd_valid),
    .actuator_cmd_ready(core_actuator_cmd_ready),
    .actuator_cmd_data(core_actuator_cmd_data),
    .fault_summary(core_fault_summary),
    .heartbeat_status(core_heartbeat_status)
  );
endmodule
