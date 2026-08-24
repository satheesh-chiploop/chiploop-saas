module adaptive_aero_controller_core (
    input clk,
    input reset_n,
    input cfg_enable,
    input [1:0] cfg_mode,
    input [15:0] cfg_timeout_cycles,
    input [15:0] cfg_command_min,
    input [15:0] cfg_command_max,
    input [15:0] cfg_speed_min,
    input [15:0] cfg_speed_max,
    input [7:0] cfg_model_req_tag,
    input [15:0] cfg_model_timeout_cycles,
    input cfg_history_capture_en,
    input cfg_fault_clear,
    input model_rsp_valid,
    input [63:0] model_rsp_data,
    output reg model_rsp_ready,
    output reg command_valid,
    output reg [15:0] command_data,
    output reg fault_latched,
    output reg status_timeout,
    output reg status_stale,
    output reg status_response_valid,
    output reg status_actuator_valid,
    output reg status_speed_valid,
    output reg [15:0] status_speed_raw,
    output reg [15:0] status_command_raw,
    output reg history_wr_en,
    output reg [63:0] history_wr_data,
    output reg [7:0] history_wr_addr
);

reg [15:0] speed_sample_reg;
reg [15:0] response_cmd_reg;
reg [15:0] age_counter_reg;
reg [7:0] history_ptr_reg;
reg seen_response_reg;

wire [15:0] model_speed_sample;
wire [7:0] model_tag_sample;
wire [15:0] model_cmd_sample;
wire speed_in_range;
wire cmd_in_range;
wire timeout_hit;
wire stale_hit;
wire response_tag_ok;

assign model_tag_sample = model_rsp_data[7:0];
assign model_speed_sample = model_rsp_data[31:16];
assign model_cmd_sample = model_rsp_data[47:32];
assign speed_in_range = (model_speed_sample >= cfg_speed_min) && (model_speed_sample <= cfg_speed_max);
assign cmd_in_range = (model_cmd_sample >= cfg_command_min) && (model_cmd_sample <= cfg_command_max);
assign timeout_hit = (age_counter_reg >= cfg_timeout_cycles) || (age_counter_reg >= cfg_model_timeout_cycles);
assign stale_hit = seen_response_reg && (age_counter_reg >= cfg_timeout_cycles);
assign response_tag_ok = (model_tag_sample == cfg_model_req_tag);

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        model_rsp_ready <= 1'b1;
        command_valid <= 1'b0;
        command_data <= 16'd0;
        fault_latched <= 1'b0;
        status_timeout <= 1'b0;
        status_stale <= 1'b0;
        status_response_valid <= 1'b0;
        status_actuator_valid <= 1'b0;
        status_speed_valid <= 1'b0;
        status_speed_raw <= 16'd0;
        status_command_raw <= 16'd0;
        history_wr_en <= 1'b0;
        history_wr_data <= 64'd0;
        history_wr_addr <= 8'd0;
        speed_sample_reg <= 16'd0;
        response_cmd_reg <= 16'd0;
        age_counter_reg <= 16'd0;
        history_ptr_reg <= 8'd0;
        seen_response_reg <= 1'b0;
    end else begin
        model_rsp_ready <= 1'b1;
        history_wr_en <= 1'b0;
        if (cfg_fault_clear) fault_latched <= 1'b0;
        if (model_rsp_valid && model_rsp_ready) begin
            speed_sample_reg <= model_speed_sample;
            response_cmd_reg <= model_cmd_sample;
            seen_response_reg <= 1'b1;
            age_counter_reg <= 16'd0;
            status_response_valid <= response_tag_ok;
            status_speed_valid <= speed_in_range;
            status_speed_raw <= model_speed_sample;
            status_command_raw <= model_cmd_sample;
            status_stale <= 1'b0;
            status_timeout <= 1'b0;
            if (!cfg_enable || !response_tag_ok || !speed_in_range || !cmd_in_range) begin
                command_valid <= 1'b0;
                fault_latched <= 1'b1;
                status_actuator_valid <= 1'b0;
            end else begin
                if (cfg_mode == 2'b00) command_data <= model_cmd_sample;
                else if (cfg_mode == 2'b01) command_data <= (model_cmd_sample < cfg_command_min) ? cfg_command_min : model_cmd_sample;
                else if (cfg_mode == 2'b10) command_data <= (model_cmd_sample > cfg_command_max) ? cfg_command_max : model_cmd_sample;
                else command_data <= model_cmd_sample ^ cfg_model_req_tag;
                if (command_data < cfg_command_min) command_data <= cfg_command_min;
                if (command_data > cfg_command_max) command_data <= cfg_command_max;
                command_valid <= 1'b1;
                status_actuator_valid <= 1'b1;
            end
            if (cfg_history_capture_en) begin
                history_wr_en <= 1'b1;
                history_wr_data <= {16'b0, cfg_model_req_tag, model_tag_sample, model_speed_sample, model_cmd_sample};
                history_wr_addr <= history_ptr_reg;
                history_ptr_reg <= history_ptr_reg + 8'd1;
            end
        end else begin
            if (age_counter_reg != 16'hFFFF) age_counter_reg <= age_counter_reg + 16'd1;
            if (timeout_hit) begin
                status_timeout <= 1'b1;
                fault_latched <= 1'b1;
                command_valid <= 1'b0;
                status_actuator_valid <= 1'b0;
            end
            if (stale_hit) begin
                status_stale <= 1'b1;
                fault_latched <= 1'b1;
                command_valid <= 1'b0;
                status_actuator_valid <= 1'b0;
            end
            if (cfg_history_capture_en) begin
                history_wr_en <= 1'b1;
                history_wr_data <= {16'b0, cfg_model_req_tag, 8'hFF, speed_sample_reg, response_cmd_reg};
                history_wr_addr <= history_ptr_reg;
                history_ptr_reg <= history_ptr_reg + 8'd1;
            end
            status_response_valid <= 1'b0;
            status_speed_valid <= (speed_sample_reg >= cfg_speed_min) && (speed_sample_reg <= cfg_speed_max);
            status_speed_raw <= speed_sample_reg;
            status_command_raw <= response_cmd_reg;
            if (!cfg_enable || fault_latched || timeout_hit || stale_hit || !((speed_sample_reg >= cfg_speed_min) && (speed_sample_reg <= cfg_speed_max))) begin
                command_valid <= 1'b0;
                status_actuator_valid <= 1'b0;
            end
        end
        if (cfg_fault_clear && !status_timeout && !status_stale && (speed_sample_reg >= cfg_speed_min) && (speed_sample_reg <= cfg_speed_max)) fault_latched <= 1'b0;
    end
end

endmodule
