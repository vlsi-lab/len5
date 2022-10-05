# Allow multi-core execution
set_host_options -max_cores 16

# Analyze packages
analyze -format sverilog -work WORK ../include/len5_pkg.sv
analyze -format sverilog -work WORK ../include/csr_pkg.sv
analyze -format sverilog -work WORK ../include/fetch_pkg.sv
analyze -format sverilog -work WORK ../include/expipe_pkg.sv
analyze -format sverilog -work WORK ../include/memory_pkg.sv

# Analyze design files
analyze -format sverilog -work WORK ../src/frontend/bpu.sv
analyze -format sverilog -work WORK ../src/frontend/gshare.sv
analyze -format sverilog -work WORK ../src/frontend/pc_gen.sv
analyze -format sverilog -work WORK ../src/frontend/fetch_mem_if.sv
analyze -format sverilog -work WORK ../src/frontend/btb.sv
analyze -format sverilog -work WORK ../src/frontend/fetch_stage.sv
analyze -format sverilog -work WORK ../src/expipe/register-file/int_regstat.sv
analyze -format sverilog -work WORK ../src/expipe/register-file/fp_regstat.sv
analyze -format sverilog -work WORK ../src/expipe/register-file/int_rf.sv
analyze -format sverilog -work WORK ../src/expipe/register-file/fp_rf.sv
analyze -format sverilog -work WORK ../src/expipe/register-file/csrs.sv
analyze -format sverilog -work WORK ../src/expipe/commit-unit/commit_stage.sv
analyze -format sverilog -work WORK ../src/expipe/commit-unit/commit_decoder.sv
analyze -format sverilog -work WORK ../src/expipe/commit-unit/commit_cu.sv
analyze -format sverilog -work WORK ../src/expipe/commit-unit/rob.sv
analyze -format sverilog -work WORK ../src/expipe/load-store-unit/store_buffer.sv
analyze -format sverilog -work WORK ../src/expipe/load-store-unit/address_adder.sv
analyze -format sverilog -work WORK ../src/expipe/load-store-unit/load_buffer.sv
analyze -format sverilog -work WORK ../src/expipe/load-store-unit/load_store_unit.sv
analyze -format sverilog -work WORK ../src/expipe/issue-unit/issue_queue.sv
analyze -format sverilog -work WORK ../src/expipe/issue-unit/issue_cu.sv
analyze -format sverilog -work WORK ../src/expipe/issue-unit/issue_decoder.sv
analyze -format sverilog -work WORK ../src/expipe/issue-unit/issue_stage.sv
analyze -format sverilog -work WORK ../src/expipe/backend.sv
analyze -format sverilog -work WORK ../src/expipe/cdb/cdb.sv
analyze -format sverilog -work WORK ../src/expipe/cdb/cdb_arbiter.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/op_only_rs.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/div.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/mult_unit.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/alu_unit.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/op_only_unit.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/div_unit.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/mult.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/alu.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/branch_rs.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/arith_rs.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/branch_unit.sv
analyze -format sverilog -work WORK ../src/expipe/exec-units/exec_stage.sv
analyze -format sverilog -work WORK ../src/datapath.sv
analyze -format sverilog -work WORK ../src/util/fifo.sv
analyze -format sverilog -work WORK ../src/util/sign_extender.sv
analyze -format sverilog -work WORK ../src/util/prio_2way_arbiter.sv
analyze -format sverilog -work WORK ../src/util/one_hot_shift_reg.sv
analyze -format sverilog -work WORK ../src/util/fair_2way_arbiter.sv
analyze -format sverilog -work WORK ../src/util/spill_cell_flush_cu.sv
analyze -format sverilog -work WORK ../src/util/spill_cell_ext.sv
analyze -format sverilog -work WORK ../src/util/ssram.sv
analyze -format sverilog -work WORK ../src/util/byte_selector.sv
analyze -format sverilog -work WORK ../src/util/fifo_comb_ready.sv
analyze -format sverilog -work WORK ../src/util/fifo_nohs.sv
analyze -format sverilog -work WORK ../src/util/spill_cell.sv
analyze -format sverilog -work WORK ../src/util/updown_counter.sv
analyze -format sverilog -work WORK ../src/util/prio_enc.sv
analyze -format sverilog -work WORK ../src/util/prio_enc_inv.sv
analyze -format sverilog -work WORK ../src/util/modn_counter.sv
analyze -format sverilog -work WORK ../src/util/spill_cell_cu.sv
analyze -format sverilog -work WORK ../src/util/spill_cell_flush.sv
analyze -format sverilog -work WORK ../src/util/age_based_sel.sv
analyze -format sverilog -work WORK ../src/util/spill_cell_ext_cu.sv

# Preserve RTL names
set power_preserve_rtl_hier_names true

# Elaborate design
redirect -tee ./logs/elaborate-log.txt {elaborate datapath -lib WORK}
uniquify
link

# create symbolic clock signal
create_clock -name CLOCK -period 0 clk_i
set_dont_touch_network CLOCK
set_clock_uncertainty 0.07 [get_clocks CLOCK]

# Set input/output delays
set_input_delay 0.5 -max -clock CLOCK [remove_from_collection [all_inputs] CLOCK]
set_output_delay 0.5 -max -clock CLOCK [all_outputs]

# Set input/output delays
set OLOAD [load_of uk65lscllmvbbr_120c25_tc/BUFM4R/A]
set_load $OLOAD [all_outputs]

# Flatten hierarchy
ungroup -all -flatten

# Start synthesis
# redirect -tee ./logs/compile-log.txt {compile_ultra}
redirect -tee ./logs/compile-log.txt {compile}

# Optimize registers
#optimize_registers
redirect -tee ./logs/optimize_registers-log.txt {optimize_registers}

# save results
redirect -tee ./reports/resources-report.txt {report_resources}
redirect -tee ./reports/timing-report.txt {report_timing}
redirect -tee ./reports/area-report.txt {report_area}
redirect -tee ./reports/power-report.txt {report_power}
