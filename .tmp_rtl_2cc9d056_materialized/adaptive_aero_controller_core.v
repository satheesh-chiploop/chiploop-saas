module adaptive_aero_controller_core (
    input         clk,
    input         reset_n,
    input         cfg_enable,
    input  [15:0] cfg_min_speed_mps,
    input  [15:0] cfg_max_speed_mps,
    input  [15:0] cfg_cmd_min,
    input  [15:0] cfg_cmd_max,
    input  [15:0] cfg_timeout_cycles,
    input  [15:0] cfg_stale_limit_cycles,
    input  [1:0]  cfg_model_select,
    input         cfg_fault_clear,
    input  [15:0] vehicle_speed_mps,
    input         sensor_valid,
    input         sensor_fault,
    input         sensor_stale,
    output reg        model_req_valid,
    output reg [63:0] model_req_data,
    input         model_req_ready,
    input         model_rsp_valid,
    input  [63:0] model_rsp_data,
    output reg        model_rsp_ready,
    output reg        actuator_cmd_valid,
    output reg [15:0] actuator_cmd_data,
    output reg        fault_latched,
    output reg        safety_inhibit,
    output reg        status_last_cmd_valid,
    output reg [15:0] status_last_cmd_data,
    output reg [15:0] status_last_speed_mps,
    output reg        status_timeout_active,
    output reg        history_wr_en,
    output reg [9:0]  history_wr_addr,
    output reg [63:0] history_wr_data,
    input  [63:0] history_rd_data
);

reg [15:0] timeout_cnt;
reg [15:0] stale_cnt;
reg [9:0] history_ptr;
reg [15:0] latched_cmd_data;
reg latched_cmd_valid;
reg [15:0] next_status_last_cmd_data;
reg next_status_last_cmd_valid;
reg [15:0] next_status_last_speed_mps;
reg next_status_timeout_active;
reg next_fault_latched;
reg next_safety_inhibit;
reg next_actuator_cmd_valid;
reg [15:0] next_actuator_cmd_data;
reg next_model_req_valid;
reg [63:0] next_model_req_data;
reg next_model_rsp_ready;
reg next_history_wr_en;
reg [9:0] next_history_wr_addr;
reg [63:0] next_history_wr_data;
wire speed_in_range;
wire sensor_ok;
wire timeout_active_int;
wire invalid_condition;
wire [15:0] raw_cmd;
wire [15:0] bounded_cmd;
wire [63:0] req_packet;
wire [63:0] hist_packet;
wire [63:0] history_mix;

assign speed_in_range = (vehicle_speed_mps >= cfg_min_speed_mps) && (vehicle_speed_mps <= cfg_max_speed_mps);
assign sensor_ok = sensor_valid && !sensor_fault && !sensor_stale;
assign timeout_active_int = (cfg_timeout_cycles != 16'd0) && (timeout_cnt >= cfg_timeout_cycles);
assign invalid_condition = (!cfg_enable) || (!speed_in_range) || (!sensor_ok) || timeout_active_int || ((cfg_stale_limit_cycles != 16'd0) && (stale_cnt >= cfg_stale_limit_cycles));
assign raw_cmd = model_rsp_data[15:0] ^ {14'b0, cfg_model_select};
assign bounded_cmd = (raw_cmd < cfg_cmd_min) ? cfg_cmd_min : ((raw_cmd > cfg_cmd_max) ? cfg_cmd_max : raw_cmd);
assign req_packet = {vehicle_speed_mps, cfg_min_speed_mps, cfg_max_speed_mps, cfg_cmd_min};
assign history_mix = model_rsp_data ^ history_rd_data;
assign hist_packet = {req_packet[31:0], history_mix[31:0]};

always @(*) begin
    next_model_rsp_ready = 1'b1;
    next_model_req_valid = cfg_enable && sensor_ok && speed_in_range && !fault_latched;
    next_model_req_data = req_packet;
    next_fault_latched = fault_latched;
    next_safety_inhibit = invalid_condition || fault_latched || (!cfg_enable);
    next_actuator_cmd_valid = 1'b0;
    next_actuator_cmd_data = actuator_cmd_data;
    next_status_last_cmd_valid = status_last_cmd_valid;
    next_status_last_cmd_data = status_last_cmd_data;
    next_status_last_speed_mps = status_last_speed_mps;
    next_status_timeout_active = timeout_active_int;
    next_history_wr_en = (next_model_req_valid && model_req_ready) || model_rsp_valid;
    next_history_wr_addr = history_ptr;
    next_history_wr_data = hist_packet;
    if (!invalid_condition && model_rsp_valid) begin
        next_actuator_cmd_valid = 1'b1;
        next_actuator_cmd_data = bounded_cmd;
        next_status_last_cmd_valid = 1'b1;
        next_status_last_cmd_data = bounded_cmd;
        next_status_last_speed_mps = vehicle_speed_mps;
        next_history_wr_en = 1'b1;
        next_history_wr_data = hist_packet ^ {48'b0, bounded_cmd};
    end
    if (invalid_condition) begin
        next_actuator_cmd_valid = 1'b0;
    end
    if (cfg_fault_clear && !invalid_condition) begin
        next_fault_latched = 1'b0;
    end else if (invalid_condition) begin
        next_fault_latched = 1'b1;
    end
end

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        model_req_valid <= 1'b0;
        model_req_data <= 64'h0000000000000000;
        model_rsp_ready <= 1'b1;
        actuator_cmd_valid <= 1'b0;
        actuator_cmd_data <= 16'h0000;
        fault_latched <= 1'b0;
        safety_inhibit <= 1'b1;
        status_last_cmd_valid <= 1'b0;
        status_last_cmd_data <= 16'h0000;
        status_last_speed_mps <= 16'h0000;
        status_timeout_active <= 1'b0;
        history_wr_en <= 1'b0;
        history_wr_addr <= 10'h000;
        history_wr_data <= 64'h0000000000000000;
        timeout_cnt <= 16'h0000;
        stale_cnt <= 16'h0000;
        history_ptr <= 10'h000;
        latched_cmd_data <= 16'h0000;
        latched_cmd_valid <= 1'b0;
    end else begin
        model_rsp_ready <= next_model_rsp_ready;
        model_req_valid <= next_model_req_valid;
        model_req_data <= next_model_req_data;
        actuator_cmd_valid <= next_actuator_cmd_valid;
        actuator_cmd_data <= next_actuator_cmd_data;
        fault_latched <= next_fault_latched;
        safety_inhibit <= next_safety_inhibit;
        status_last_cmd_valid <= next_status_last_cmd_valid;
        status_last_cmd_data <= next_status_last_cmd_data;
        status_last_speed_mps <= next_status_last_speed_mps;
        status_timeout_active <= next_status_timeout_active;
        history_wr_en <= next_history_wr_en;
        history_wr_addr <= next_history_wr_addr;
        history_wr_data <= next_history_wr_data;

        if (sensor_valid && !sensor_fault && !sensor_stale) begin
            stale_cnt <= 16'h0000;
        end else if (stale_cnt != 16'hffff) begin
            stale_cnt <= stale_cnt + 16'h0001;
        end

        if (cfg_enable && sensor_ok && speed_in_range && !fault_latched) begin
            if (model_req_ready) begin
                timeout_cnt <= 16'h0000;
            end else if (timeout_cnt != 16'hffff) begin
                timeout_cnt <= timeout_cnt + 16'h0001;
            end
        end else begin
            timeout_cnt <= 16'h0000;
        end

        if (history_wr_en) begin
            history_ptr <= history_ptr + 10'h001;
        end

        if (next_actuator_cmd_valid) begin
            latched_cmd_data <= next_actuator_cmd_data;
            latched_cmd_valid <= 1'b1;
        end
    end
end

endmodule