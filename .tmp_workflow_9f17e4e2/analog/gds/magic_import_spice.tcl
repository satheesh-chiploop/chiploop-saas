drc off
source /pdk/sky130A/libs.tech/magic/sky130A.tcl
load temp_sensor_adc_model
select top cell
box 0 0 8000 6240
puts stdout "CHIPLOOP_FINAL_BOX=[box values]"
puts stdout "CHIPLOOP_FLAT_BOX=[box values]"
set chiploop_flat_bbox [box values]
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (0 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[0]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (1 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[1]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (2 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[2]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (3 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[3]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (4 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[4]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (5 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[5]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (6 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[6]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (7 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[7]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (8 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[8]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (9 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[9]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (10 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[10]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (11 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_code[11]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (12 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[0]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (13 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[1]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (14 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[2]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (15 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[3]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (16 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[4]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (17 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[5]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (18 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[6]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (19 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[7]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (20 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[8]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (21 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[9]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (22 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[10]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (23 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[11]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (24 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[12]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (25 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[13]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (26 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[14]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (27 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sensor_temp_celsius[15]} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (28 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {VGND} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (29 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {VPWR} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (30 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {adc_valid} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (31 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {avdd} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (32 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {avss} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
set chiploop_port_x [expr {[lindex $chiploop_flat_bbox 2] + 400}]
set chiploop_port_y [expr {[lindex $chiploop_flat_bbox 3] + 400 + (33 * 160)}]
select clear
box $chiploop_port_x $chiploop_port_y [expr {$chiploop_port_x + 80}] [expr {$chiploop_port_y + 80}]
paint m2
label {sample_req} FreeSans 200 0 0 0 center m2
select area labels
port make
select clear
catch {gds flatten true}
catch {gds flatglob *}
catch {feedback save magic_feedback.txt}
save temp_sensor_adc_model.mag
gds write temp_sensor_adc_model.gds
catch {feedback save magic_feedback.txt}
quit -noprompt
