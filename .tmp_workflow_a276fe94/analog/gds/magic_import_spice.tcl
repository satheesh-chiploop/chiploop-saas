drc off
source /pdk/sky130A/libs.tech/magic/sky130A.tcl
magic::netlist_to_layout temp_sensor_adc_model.sp sky130
load temp_sensor_adc_model
select top cell
expand
puts stdout "CHIPLOOP_FINAL_BOX=[box values]"
flatten temp_sensor_adc_model_flat
load temp_sensor_adc_model_flat
select top cell
expand
puts stdout "CHIPLOOP_FLAT_BOX=[box values]"
catch {feedback save magic_feedback.txt}
save temp_sensor_adc_model.mag
gds write temp_sensor_adc_model.gds
catch {feedback save magic_feedback.txt}
quit -noprompt
