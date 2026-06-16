drc off
gds read /work/temp_sensor_adc_model.gds
load temp_sensor_adc_model
select top cell
lef write /work/temp_sensor_adc_model.lef
quit -noprompt
