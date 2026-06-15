# Auto-generated fallback by Digital Implementation Setup Agent
create_clock -name clk -period 20.000 [get_ports clk]
# set_false_path -from [get_ports reset_n]

# ChipLoop synthesis closure iteration 1: tool-only setup repair guidance.
# No RTL edits, ECO edits, or design-specific constraints are applied.
if {[llength [all_registers]] > 0} {
  catch {group_path -name chiploop_reg2reg_closure -from [all_registers] -to [all_registers] -critical_range 1.000 -weight 3}
}
if {[llength [all_inputs]] > 0 && [llength [all_registers]] > 0} {
  catch {group_path -name chiploop_in2reg_closure -from [all_inputs] -to [all_registers] -critical_range 1.000 -weight 2}
}
if {[llength [all_registers]] > 0 && [llength [all_outputs]] > 0} {
  catch {group_path -name chiploop_reg2out_closure -from [all_registers] -to [all_outputs] -critical_range 1.000 -weight 2}
}
catch {set_max_fanout 8 [current_design]}
