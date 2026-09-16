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
  localparam integer INPUT_BITS = 208;
  localparam integer OUTPUT_BITS = 181;
  localparam integer FRAME_BITS = 208;
  logic [FRAME_BITS-1:0] rx_shift;
  logic [INPUT_BITS-1:0] rx_active;
  logic [FRAME_BITS-1:0] tx_shift, tx_snapshot;
  logic spi_active;
  logic spi_cs_meta, spi_cs_sync, spi_cs_prev;
  logic core_spi_cs_n;
  logic core_spi_sclk;
  logic core_spi_mosi;
  logic core_host_cmd_valid;
  logic [7:0] core_host_cmd_opcode;
  logic [31:0] core_host_cmd_data;
  logic core_host_rsp_ready;
  logic core_model_req_ready;
  logic core_model_rsp_valid;
  logic [31:0] core_model_rsp_data;
  logic core_sensor_airdata_valid;
  logic [15:0] core_sensor_airspeed;
  logic [15:0] core_sensor_altitude;
  logic [15:0] core_sensor_angle_of_attack;
  logic [15:0] core_sensor_gload;
  logic [31:0] core_history_dout;
  logic [31:0] core_payload_dout;
  wire core_spi_miso;
  wire core_host_rsp_valid;
  wire [31:0] core_host_rsp_data;
  wire core_host_fault_valid;
  wire core_model_req_valid;
  wire [31:0] core_model_req_data;
  wire core_model_rsp_ready;
  wire core_actuator_cmd_valid;
  wire [15:0] core_actuator_cmd_data;
  wire core_actuator_cmd_saturated;
  wire core_actuator_cmd_latched_fault;
  wire core_status_valid;
  wire [7:0] core_status_code;
  wire core_fault_latched;
  wire core_history_csb_n;
  wire core_history_we_n;
  wire [7:0] core_history_addr;
  wire [31:0] core_history_din;
  wire core_payload_csb_n;
  wire core_payload_we_n;
  wire [6:0] core_payload_addr;
  wire [31:0] core_payload_din;
  assign core_spi_cs_n = rx_active[0 +: 1];
  assign core_spi_sclk = rx_active[1 +: 1];
  assign core_spi_mosi = rx_active[2 +: 1];
  assign core_host_cmd_valid = rx_active[3 +: 1];
  assign core_host_cmd_opcode = rx_active[4 +: 8];
  assign core_host_cmd_data = rx_active[12 +: 32];
  assign core_host_rsp_ready = rx_active[44 +: 1];
  assign core_model_req_ready = rx_active[45 +: 1];
  assign core_model_rsp_valid = rx_active[46 +: 1];
  assign core_model_rsp_data = rx_active[47 +: 32];
  assign core_sensor_airdata_valid = rx_active[79 +: 1];
  assign core_sensor_airspeed = rx_active[80 +: 16];
  assign core_sensor_altitude = rx_active[96 +: 16];
  assign core_sensor_angle_of_attack = rx_active[112 +: 16];
  assign core_sensor_gload = rx_active[128 +: 16];
  assign core_history_dout = rx_active[144 +: 32];
  assign core_payload_dout = rx_active[176 +: 32];
  wire [OUTPUT_BITS-1:0] core_response = {core_spi_miso, core_host_rsp_valid, core_host_rsp_data, core_host_fault_valid, core_model_req_valid, core_model_req_data, core_model_rsp_ready, core_actuator_cmd_valid, core_actuator_cmd_data, core_actuator_cmd_saturated, core_actuator_cmd_latched_fault, core_status_valid, core_status_code, core_fault_latched, core_history_csb_n, core_history_we_n, core_history_addr, core_history_din, core_payload_csb_n, core_payload_we_n, core_payload_addr, core_payload_din};
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
    .reset_n(reset_n),
    .spi_cs_n(core_spi_cs_n),
    .spi_sclk(core_spi_sclk),
    .spi_mosi(core_spi_mosi),
    .spi_miso(core_spi_miso),
    .host_cmd_valid(core_host_cmd_valid),
    .host_cmd_opcode(core_host_cmd_opcode),
    .host_cmd_data(core_host_cmd_data),
    .host_rsp_ready(core_host_rsp_ready),
    .host_rsp_valid(core_host_rsp_valid),
    .host_rsp_data(core_host_rsp_data),
    .host_fault_valid(core_host_fault_valid),
    .model_req_valid(core_model_req_valid),
    .model_req_data(core_model_req_data),
    .model_req_ready(core_model_req_ready),
    .model_rsp_valid(core_model_rsp_valid),
    .model_rsp_data(core_model_rsp_data),
    .model_rsp_ready(core_model_rsp_ready),
    .actuator_cmd_valid(core_actuator_cmd_valid),
    .actuator_cmd_data(core_actuator_cmd_data),
    .actuator_cmd_saturated(core_actuator_cmd_saturated),
    .actuator_cmd_latched_fault(core_actuator_cmd_latched_fault),
    .sensor_airdata_valid(core_sensor_airdata_valid),
    .sensor_airspeed(core_sensor_airspeed),
    .sensor_altitude(core_sensor_altitude),
    .sensor_angle_of_attack(core_sensor_angle_of_attack),
    .sensor_gload(core_sensor_gload),
    .status_valid(core_status_valid),
    .status_code(core_status_code),
    .fault_latched(core_fault_latched),
    .history_csb_n(core_history_csb_n),
    .history_we_n(core_history_we_n),
    .history_addr(core_history_addr),
    .history_din(core_history_din),
    .history_dout(core_history_dout),
    .payload_csb_n(core_payload_csb_n),
    .payload_we_n(core_payload_we_n),
    .payload_addr(core_payload_addr),
    .payload_din(core_payload_din),
    .payload_dout(core_payload_dout)
  );
endmodule
