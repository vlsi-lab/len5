# Set the constraints file
set SET_LIBS ${SCRIPT_DIR}/set-libs.tcl
set SET_CONSTRAINTS ${SCRIPT_DIR}/set-constraints.tcl
# Utility procedures
set UTILS ${SCRIPT_DIR}/utils.tcl

source ${SET_LIBS}
source ${READ_SOURCES}.tcl
source ${UTILS}

elaborate ${TOP_MODULE}

# Link design
link

# Store precompiled netlist + constraints
write -format ddc -hierarchy -output ${REPORT_DIR}/precompiled.ddc

# Set timing constraints
source ${SET_CONSTRAINTS}

# Report clocks and combinational loops
report_clocks > ${REPORT_DIR}/clocks.rpt
report_timing -loop -max_paths 10 > ${REPORT_DIR}/timing_loop.rpt

# Check for combinational loops and exit if it finds one
timing_loop_check "${REPORT_DIR}/timing_loop.rpt"

# Setup clock-gating style
set_clock_gating_style -minimum_bitwidth 3 -positive_edge_logic integrated:CKLNQD16LVT -control_point before

# Check the design
check_design > ${REPORT_DIR}/check_design.log

# Compile design
compile_ultra -no_autoungroup -no_boundary_optimization -timing -gate_clock

# Store compiled netlist + constraints
write -f ddc -hierarchy -output ${REPORT_DIR}/compiled.ddc

# Write synthesized netlist
change_names -rules verilog -hier
# Check the design for potential problems
check_design > ${REPORT_DIR}/check_design.rpt

write -format verilog -hier -o ${REPORT_DIR}/netlist.v

# Write SDC and SDF files
write_sdc -version 1.7 ${REPORT_DIR}/netlist.sdc
write_sdf -version 2.1 ${REPORT_DIR}/netlist.sdf

# Generate reports
report_timing -nosplit -max_paths 10 > ${REPORT_DIR}/timing.rpt
report_timing -nosplit -delay_type min -max_paths 10 > ${REPORT_DIR}/timing-fast.rpt
report_area -hier -nosplit > ${REPORT_DIR}/area.rpt
report_resources -hierarchy > ${REPORT_DIR}/resources.rpt
report_constraints > ${REPORT_DIR}/constraints.rpt
report_clock_gating > ${REPORT_DIR}/clock_gating.rpt
report_timing -nosplit -from [all_inputs] -to [all_outputs] > ${REPORT_DIR}/in-out-paths.rpt
