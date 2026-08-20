module adaptive_aero_control_top (
    input         clk,
    input         reset_n,
    input  [7:0] wb_adr_i,
    input  [31:0] wb_dat_i,
    output [31:0] wb_dat_o,
    input         wb_we_i,
    input         wb_stb_i,
    input         wb_cyc_i,
    output        wb_ack_o,
    output        wb_err_o,
    input  [3:0] wb_sel_i,
    output        req_valid_o,
    input         req_ready_i,
    output [127:0] req_payload_o,
    input         rsp_valid_i,
    output        rsp_ready_o,
    input  [127:0] rsp_payload_i,
    output [31:0] actuator_cmd_o,
    output        fault_o,
    output        irq_o
);

  localparam [7:0] ADDR_CONTROL           = 8'h00;
  localparam [7:0] ADDR_STATUS            = 8'h04;
  localparam [7:0] ADDR_TIMEOUT           = 8'h08;
  localparam [7:0] ADDR_VELO_LIMIT_MIN    = 8'h0C;
  localparam [7:0] ADDR_VELO_LIMIT_MAX    = 8'h10;
  localparam [7:0] ADDR_SEQUENCE          = 8'h14;
  localparam [7:0] ADDR_LAST_REQUEST      = 8'h18;
  localparam [7:0] ADDR_LAST_RESPONSE     = 8'h1C;
  localparam [7:0] ADDR_ACTUATOR_CLAMP_MIN= 8'h20;
  localparam [7:0] ADDR_ACTUATOR_CLAMP_MAX= 8'h24;
  localparam [7:0] ADDR_ACTUATOR_COMMAND  = 8'h28;
  localparam [7:0] ADDR_FAULT_CLEAR       = 8'h2C;
  localparam [7:0] ADDR_REQUEST_TYPE      = 8'h30;
  localparam [7:0] ADDR_GEOMETRY_HANDLE   = 8'h34;
  localparam [7:0] ADDR_FLOW_CONDITION    = 8'h38;
  localparam [7:0] ADDR_TELEMETRY         = 8'h3C;

  localparam [2:0] ST_IDLE          = 3'd0;
  localparam [2:0] ST_LAUNCH        = 3'd1;
  localparam [2:0] ST_WAIT_RSP      = 3'd2;
  localparam [2:0] ST_VALIDATE_RSP  = 3'd3;
  localparam [2:0] ST_UPDATE_CMD    = 3'd4;
  localparam [2:0] ST_SAFE_FALLBACK = 3'd5;
  localparam [2:0] ST_FAULT_LATCHED = 3'd6;

  reg [7:0]  control_reg;
  reg [31:0] timeout_reg;
  reg [15:0] velo_min_reg;
  reg [15:0] velo_max_reg;
  reg [15:0] sequence_reg;
  reg [31:0] actuator_clamp_min_reg;
  reg [31:0] actuator_clamp_max_reg;
  reg [1:0]  request_type_reg;
  reg [7:0]  geometry_handle_reg;
  reg [15:0] flow_condition_reg;

  reg [15:0] last_request_sequence_reg;
  reg [1:0]  last_request_type_reg;
  reg [7:0]  last_request_geometry_handle_reg;
  reg [5:0]  last_request_velocity_reg;

  reg [15:0] last_response_sequence_reg;
  reg [7:0]  last_response_summary_reg;
  reg [7:0]  last_response_age_reg;

  reg [31:0] last_accepted_actuator_command_reg;
  reg [15:0] transaction_age_reg;
  reg [3:0]  last_reject_reason_reg;

  reg [2:0]  state_reg;
  reg [31:0] timeout_count_reg;
  reg        req_valid_reg;
  reg [127:0] req_payload_reg;
  reg        rsp_ready_reg;
  reg [31:0] actuator_cmd_reg;
  reg        fault_reg;
  reg        irq_reg;
  reg        outstanding_reg;
  reg        response_received_reg;
  reg        timeout_error_reg;
  reg        stale_error_reg;
  reg        clamp_active_reg;
  reg        safe_fallback_active_reg;
  reg        last_response_valid_reg;
  reg        last_response_match_reg;
  reg        last_reject_is_timeout_reg;
  reg        last_reject_is_stale_reg;
  reg        last_reject_is_malformed_reg;
  reg        last_reject_is_sequence_mismatch_reg;

  wire wb_valid;
  wire wb_write;
  wire wb_read;
  wire wb_sel_any;
  wire launch_pulse;
  wire clear_fault_pulse;
  wire fault_clear_pulse;
  wire [31:0] wb_read_data;
  wire wb_err_next;
  wire wb_ack_next;
  reg  [31:0] wb_read_mux;

  wire [15:0] req_velocity_field;
  wire [7:0]  req_flow_field;
  wire [15:0] rsp_seq_field;
  wire [7:0]  rsp_summary_field;
  wire [7:0]  rsp_age_field;
  wire        rsp_struct_valid;
  wire [31:0] cmd_clamped_next;
  wire [31:0] fallback_cmd;
  wire [31:0] raw_cmd_candidate;
  wire        velocity_in_range;
  wire        timeout_expired;
  wire        stale_expired;
  wire        rsp_seq_match;
  wire        rsp_age_valid;

  assign wb_valid = wb_stb_i & wb_cyc_i;
  assign wb_write = wb_valid & wb_we_i;
  assign wb_read  = wb_valid & ~wb_we_i;
  assign wb_sel_any = |wb_sel_i;
  assign launch_pulse = wb_write & wb_sel_any & (wb_adr_i == ADDR_CONTROL) & wb_dat_i[1];
  assign clear_fault_pulse = wb_write & wb_sel_any & ((wb_adr_i == ADDR_CONTROL) ? wb_dat_i[2] : 1'b0);
  assign fault_clear_pulse = clear_fault_pulse | (wb_write & wb_sel_any & (wb_adr_i == ADDR_FAULT_CLEAR) & wb_dat_i[0]);

  assign req_velocity_field = {10'b0000000000, velo_max_reg[5:0]};
  assign req_flow_field = flow_condition_reg[7:0];
  assign rsp_seq_field = rsp_payload_i[15:0];
  assign rsp_summary_field = rsp_payload_i[23:16];
  assign rsp_age_field = rsp_payload_i[31:24];
  assign rsp_struct_valid = rsp_valid_i & rsp_payload_i[32];
  assign rsp_seq_match = (rsp_seq_field == sequence_reg);
  assign rsp_age_valid = (rsp_age_field <= timeout_reg[7:0]);
  assign velocity_in_range = (velo_min_reg <= velo_max_reg) && (velo_min_reg >= 16'd20) && (velo_max_reg <= 16'd55);
  assign timeout_expired = (timeout_count_reg >= timeout_reg);
  assign stale_expired = (rsp_age_field > timeout_reg[31:16]);
  assign raw_cmd_candidate = {24'b0, rsp_summary_field};
  assign fallback_cmd = {32{1'b0}};
  assign cmd_clamped_next = (raw_cmd_candidate < actuator_clamp_min_reg) ? actuator_clamp_min_reg :
                            (raw_cmd_candidate > actuator_clamp_max_reg) ? actuator_clamp_max_reg :
                            raw_cmd_candidate;

  assign wb_err_next = wb_valid & wb_sel_any & ~(
                        (wb_adr_i == ADDR_CONTROL) ||
                        (wb_adr_i == ADDR_STATUS) ||
                        (wb_adr_i == ADDR_TIMEOUT) ||
                        (wb_adr_i == ADDR_VELO_LIMIT_MIN) ||
                        (wb_adr_i == ADDR_VELO_LIMIT_MAX) ||
                        (wb_adr_i == ADDR_SEQUENCE) ||
                        (wb_adr_i == ADDR_LAST_REQUEST) ||
                        (wb_adr_i == ADDR_LAST_RESPONSE) ||
                        (wb_adr_i == ADDR_ACTUATOR_CLAMP_MIN) ||
                        (wb_adr_i == ADDR_ACTUATOR_CLAMP_MAX) ||
                        (wb_adr_i == ADDR_ACTUATOR_COMMAND) ||
                        (wb_adr_i == ADDR_FAULT_CLEAR) ||
                        (wb_adr_i == ADDR_REQUEST_TYPE) ||
                        (wb_adr_i == ADDR_GEOMETRY_HANDLE) ||
                        (wb_adr_i == ADDR_FLOW_CONDITION) ||
                        (wb_adr_i == ADDR_TELEMETRY)
                      );
  assign wb_ack_next = wb_valid & (wb_sel_any & ~wb_err_next);

  assign wb_dat_o = wb_read_data;
  assign wb_ack_o = wb_ack_next;
  assign wb_err_o = wb_err_next;
  assign req_valid_o = req_valid_reg;
  assign req_payload_o = req_payload_reg;
  assign rsp_ready_o = rsp_ready_reg;
  assign actuator_cmd_o = actuator_cmd_reg;
  assign fault_o = fault_reg;
  assign irq_o = irq_reg;

  always @(*) begin
    wb_read_mux = 32'h00000000;
    case (wb_adr_i)
      ADDR_CONTROL: begin
        wb_read_mux = {24'h000000, control_reg};
      end
      ADDR_STATUS: begin
        wb_read_mux = {13'b0, last_reject_is_sequence_mismatch_reg, last_reject_is_malformed_reg, last_reject_is_stale_reg, last_reject_is_timeout_reg, last_response_match_reg, last_response_valid_reg, fault_reg, safe_fallback_active_reg, clamp_active_reg, stale_error_reg, timeout_error_reg, response_received_reg, outstanding_reg, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0};
      end
      ADDR_TIMEOUT: begin
        wb_read_mux = timeout_reg;
      end
      ADDR_VELO_LIMIT_MIN: begin
        wb_read_mux = {16'h0000, velo_min_reg};
      end
      ADDR_VELO_LIMIT_MAX: begin
        wb_read_mux = {16'h0000, velo_max_reg};
      end
      ADDR_SEQUENCE: begin
        wb_read_mux = {16'h0000, sequence_reg};
      end
      ADDR_LAST_REQUEST: begin
        wb_read_mux = {last_request_velocity_reg, last_request_geometry_handle_reg, last_request_type_reg, last_request_sequence_reg};
      end
      ADDR_LAST_RESPONSE: begin
        wb_read_mux = {last_response_age_reg, last_response_summary_reg, last_response_sequence_reg};
      end
      ADDR_ACTUATOR_CLAMP_MIN: begin
        wb_read_mux = actuator_clamp_min_reg;
      end
      ADDR_ACTUATOR_CLAMP_MAX: begin
        wb_read_mux = actuator_clamp_max_reg;
      end
      ADDR_ACTUATOR_COMMAND: begin
        wb_read_mux = last_accepted_actuator_command_reg;
      end
      ADDR_REQUEST_TYPE: begin
        wb_read_mux = {30'h00000000, request_type_reg};
      end
      ADDR_GEOMETRY_HANDLE: begin
        wb_read_mux = {24'h000000, geometry_handle_reg};
      end
      ADDR_FLOW_CONDITION: begin
        wb_read_mux = {16'h0000, flow_condition_reg};
      end
      ADDR_TELEMETRY: begin
        wb_read_mux = {6'b0, irq_reg, outstanding_reg, last_reject_reason_reg, transaction_age_reg, 1'b0, 1'b0, 1'b0, 1'b0};
      end
      default: begin
        wb_read_mux = 32'h00000000;
      end
    endcase
  end

  assign wb_read_data = wb_read_mux;

  always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      control_reg <= 8'h00;
      timeout_reg <= 32'd1000;
      velo_min_reg <= 16'd20;
      velo_max_reg <= 16'd55;
      sequence_reg <= 16'd0;
      actuator_clamp_min_reg <= 32'd0;
      actuator_clamp_max_reg <= 32'd4095;
      request_type_reg <= 2'd0;
      geometry_handle_reg <= 8'd0;
      flow_condition_reg <= 16'd0;
      last_request_sequence_reg <= 16'd0;
      last_request_type_reg <= 2'd0;
      last_request_geometry_handle_reg <= 8'd0;
      last_request_velocity_reg <= 6'd0;
      last_response_sequence_reg <= 16'd0;
      last_response_summary_reg <= 8'd0;
      last_response_age_reg <= 8'd0;
      last_accepted_actuator_command_reg <= 32'd0;
      transaction_age_reg <= 16'd0;
      last_reject_reason_reg <= 4'd0;
      state_reg <= ST_IDLE;
      timeout_count_reg <= 32'd0;
      req_valid_reg <= 1'b0;
      req_payload_reg <= 128'd0;
      rsp_ready_reg <= 1'b1;
      actuator_cmd_reg <= 32'd0;
      fault_reg <= 1'b0;
      irq_reg <= 1'b0;
      outstanding_reg <= 1'b0;
      response_received_reg <= 1'b0;
      timeout_error_reg <= 1'b0;
      stale_error_reg <= 1'b0;
      clamp_active_reg <= 1'b0;
      safe_fallback_active_reg <= 1'b1;
      last_response_valid_reg <= 1'b0;
      last_response_match_reg <= 1'b0;
      last_reject_is_timeout_reg <= 1'b0;
      last_reject_is_stale_reg <= 1'b0;
      last_reject_is_malformed_reg <= 1'b0;
      last_reject_is_sequence_mismatch_reg <= 1'b0;
    end else begin
      req_valid_reg <= 1'b0;
      rsp_ready_reg <= 1'b1;
      irq_reg <= 1'b0;

      if (wb_write && wb_sel_any) begin
        case (wb_adr_i)
          ADDR_CONTROL: begin
            control_reg[0] <= wb_dat_i[0];
            control_reg[3] <= wb_dat_i[3];
            control_reg[4] <= wb_dat_i[4];
          end
          ADDR_TIMEOUT: begin
            timeout_reg <= wb_dat_i;
          end
          ADDR_VELO_LIMIT_MIN: begin
            velo_min_reg <= wb_dat_i[15:0];
          end
          ADDR_VELO_LIMIT_MAX: begin
            velo_max_reg <= wb_dat_i[15:0];
          end
          ADDR_SEQUENCE: begin
            sequence_reg <= wb_dat_i[15:0];
          end
          ADDR_ACTUATOR_CLAMP_MIN: begin
            actuator_clamp_min_reg <= wb_dat_i;
          end
          ADDR_ACTUATOR_CLAMP_MAX: begin
            actuator_clamp_max_reg <= wb_dat_i;
          end
          ADDR_FAULT_CLEAR: begin
            if (wb_dat_i[0]) begin
              fault_reg <= 1'b0;
              timeout_error_reg <= 1'b0;
              stale_error_reg <= 1'b0;
              clamp_active_reg <= 1'b0;
              safe_fallback_active_reg <= 1'b0;
              last_reject_reason_reg <= 4'd0;
              last_reject_is_timeout_reg <= 1'b0;
              last_reject_is_stale_reg <= 1'b0;
              last_reject_is_malformed_reg <= 1'b0;
              last_reject_is_sequence_mismatch_reg <= 1'b0;
            end
          end
          ADDR_REQUEST_TYPE: begin
            request_type_reg <= wb_dat_i[1:0];
          end
          ADDR_GEOMETRY_HANDLE: begin
            geometry_handle_reg <= wb_dat_i[7:0];
          end
          ADDR_FLOW_CONDITION: begin
            flow_condition_reg <= wb_dat_i[15:0];
          end
          ADDR_CONTROL: begin
            if (wb_dat_i[2]) begin
              fault_reg <= 1'b0;
              timeout_error_reg <= 1'b0;
              stale_error_reg <= 1'b0;
              clamp_active_reg <= 1'b0;
              safe_fallback_active_reg <= 1'b0;
              last_reject_reason_reg <= 4'd0;
              last_reject_is_timeout_reg <= 1'b0;
              last_reject_is_stale_reg <= 1'b0;
              last_reject_is_malformed_reg <= 1'b0;
              last_reject_is_sequence_mismatch_reg <= 1'b0;
            end
          end
          default: begin
          end
        endcase
      end

      if (wb_write && wb_sel_any && wb_adr_i == ADDR_CONTROL) begin
        control_reg[0] <= wb_dat_i[0];
      end

      if (launch_pulse && control_reg[0] && ~outstanding_reg && velocity_in_range && ~fault_reg) begin
        req_valid_reg <= 1'b1;
        req_payload_reg <= {16'b0, 64'd0, flow_condition_reg, geometry_handle_reg, request_type_reg, sequence_reg, velo_max_reg[5:0]};
        last_request_sequence_reg <= sequence_reg;
        last_request_type_reg <= request_type_reg;
        last_request_geometry_handle_reg <= geometry_handle_reg;
        last_request_velocity_reg <= velo_max_reg[5:0];
        outstanding_reg <= 1'b1;
        response_received_reg <= 1'b0;
        timeout_count_reg <= 32'd0;
        transaction_age_reg <= 16'd0;
        safe_fallback_active_reg <= 1'b0;
        last_response_valid_reg <= 1'b0;
        last_response_match_reg <= 1'b0;
        state_reg <= ST_WAIT_RSP;
      end else if (launch_pulse && (~control_reg[0] || outstanding_reg || ~velocity_in_range || fault_reg)) begin
        fault_reg <= fault_reg | ~velocity_in_range;
        safe_fallback_active_reg <= 1'b1;
        last_reject_reason_reg <= ~velocity_in_range ? 4'd3 : 4'd4;
        last_reject_is_malformed_reg <= ~velocity_in_range;
        state_reg <= ST_FAULT_LATCHED;
      end

      if (outstanding_reg) begin
        timeout_count_reg <= timeout_count_reg + 32'd1;
        transaction_age_reg <= transaction_age_reg + 16'd1;
      end

      if (outstanding_reg && timeout_expired) begin
        fault_reg <= 1'b1;
        timeout_error_reg <= 1'b1;
        safe_fallback_active_reg <= 1'b1;
        last_reject_reason_reg <= 4'd1;
        last_reject_is_timeout_reg <= 1'b1;
        outstanding_reg <= 1'b0;
        req_valid_reg <= 1'b0;
        state_reg <= ST_SAFE_FALLBACK;
      end

      if (rsp_valid_i) begin
        last_response_sequence_reg <= rsp_seq_field;
        last_response_summary_reg <= rsp_summary_field;
        last_response_age_reg <= rsp_age_field;
        last_response_valid_reg <= rsp_struct_valid;
        if (outstanding_reg && rsp_struct_valid && rsp_seq_match && rsp_age_valid && ~timeout_expired) begin
          last_response_match_reg <= 1'b1;
          response_received_reg <= 1'b1;
          clamp_active_reg <= (cmd_clamped_next != raw_cmd_candidate);
          actuator_cmd_reg <= cmd_clamped_next;
          last_accepted_actuator_command_reg <= cmd_clamped_next;
          safe_fallback_active_reg <= 1'b0;
          outstanding_reg <= 1'b0;
          transaction_age_reg <= rsp_age_field;
          state_reg <= ST_UPDATE_CMD;
        end else begin
          fault_reg <= 1'b1;
          safe_fallback_active_reg <= 1'b1;
          last_response_match_reg <= 1'b0;
          if (~rsp_struct_valid) begin
            last_reject_reason_reg <= 4'd2;
            last_reject_is_malformed_reg <= 1'b1;
          end else if (~rsp_seq_match) begin
            last_reject_reason_reg <= 4'd4;
            last_reject_is_sequence_mismatch_reg <= 1'b1;
          end else if (~rsp_age_valid) begin
            last_reject_reason_reg <= 4'd3;
            last_reject_is_stale_reg <= 1'b1;
            stale_error_reg <= 1'b1;
          end else begin
            last_reject_reason_reg <= 4'd2;
            last_reject_is_malformed_reg <= 1'b1;
          end
          outstanding_reg <= 1'b0;
          state_reg <= ST_FAULT_LATCHED;
        end
      end

      if (control_reg[0] == 1'b0) begin
        safe_fallback_active_reg <= 1'b1;
      end

      if (fault_clear_pulse) begin
        fault_reg <= 1'b0;
        timeout_error_reg <= 1'b0;
        stale_error_reg <= 1'b0;
        clamp_active_reg <= 1'b0;
        safe_fallback_active_reg <= 1'b0;
        last_reject_reason_reg <= 4'd0;
        last_reject_is_timeout_reg <= 1'b0;
        last_reject_is_stale_reg <= 1'b0;
        last_reject_is_malformed_reg <= 1'b0;
        last_reject_is_sequence_mismatch_reg <= 1'b0;
        state_reg <= ST_IDLE;
      end

      if (fault_reg && control_reg[3] && (last_reject_reason_reg != 4'd0)) begin
        irq_reg <= 1'b1;
      end
      if (response_received_reg && control_reg[3] && control_reg[4]) begin
        irq_reg <= 1'b1;
      end
    end
  end

endmodule
