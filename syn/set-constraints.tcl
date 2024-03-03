# Clock period (in ns)
#set CLK_PERIOD 2
set CLK_PERIOD 0

# Memory timing (based on TSMC65 SRAMs)
set MEM_INPUT_DELAY 2.2
set MEM_OUTPUT_DELAY 0.4

# Other inputs
if {$CLK_PERIOD == 0} {
    # Assume 1ns
    set INPUT_DELAY 1
    set OUTPUT_DELAY 1
} else {
    # Assume half clock cycle
    set INPUT_DELAY [expr $CLK_PERIOD / 2]
    set OUTPUT_DELAY [expr $CLK_PERIOD / 2]
}

# Output load
set OLOAD [load_of tcbn65lpwc/BUFFD24/I]

# Reset signal is a false path
set_false_path -from [get_ports rst_ni]

# Clock
create_clock -name "CLK" -period $CLK_PERIOD [get_ports clk_i]

# Input and output delays
set MEM_INPUTS [get_ports {instr_rdata_i data_load_rdata_i}]
set MEM_OUTPUTS [get_ports {instr_addr_o instr_req_o instr_we_o data_load_req_o data_load_we_o data_load_addr_o data_load_be_o data_store_req_o data_store_we_o data_store_addr_o data_store_be_o data_store_wdata_o}]
set_input_delay -clock CLK -max $MEM_INPUT_DELAY $MEM_INPUTS
set_output_delay -clock CLK -max $MEM_OUTPUT_DELAY $MEM_OUTPUTS

set EXCLUDED_INPUTS [get_ports {rst_ni}]
set DELAYED_INPUTS [remove_from_collection [all_inputs] [concat $EXCLUDED_INPUTS $MEM_INPUTS]]
set DELAYED_OUTPUTS [remove_from_collection [all_outputs] $MEM_OUTPUTS]
set_input_delay -clock CLK -max $INPUT_DELAY $DELAYED_INPUTS
set_output_delay -clock CLK -max $OUTPUT_DELAY $DELAYED_OUTPUTS
set_load $OLOAD [all_outputs]

# Clean up
unset INPUT_DELAY EXCLUDED_INPUTS DELAYED_INPUTS DELAYED_OUTPUTS MEM_INPUTS MEM_OUTPUTS
