drc off
source /pdk/sky130A/libs.tech/magic/sky130A.tcl
magic::netlist_to_layout temp_sensor_adc_model.sp sky130
load temp_sensor_adc_model
select top cell
expand
puts stdout "CHIPLOOP_FINAL_BOX=[box values]"
flatten temp_sensor_adc_model_flat
load temp_sensor_adc_model_flat
catch {cellname delete temp_sensor_adc_model} chiploop_delete_original_result
puts stdout "CHIPLOOP_DELETE_ORIGINAL_RESULT=$chiploop_delete_original_result"
cellname rename temp_sensor_adc_model_flat temp_sensor_adc_model
load temp_sensor_adc_model
select top cell
expand
puts stdout "CHIPLOOP_FLAT_BOX=[box values]"
gds flatten true
catch {gds flatglob *}
catch {feedback save magic_feedback.txt}
save temp_sensor_adc_model.mag
gds write temp_sensor_adc_model.gds
catch {feedback save magic_feedback.txt}
quit -noprompt
