drc off
source /pdk/sky130A/libs.tech/magic/sky130A.tcl
load temp_sensor_adc_model
extract all
ext2spice lvs
ext2spice cthresh 0
ext2spice extresist off
ext2spice -o temp_sensor_adc_model_extracted.spice
quit -noprompt
