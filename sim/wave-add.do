onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_with_l2cemu/clk
add wave -noupdate /tb_with_l2cemu/rst_n
add wave -noupdate /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_instr_o.raw
add wave -noupdate /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/comm_reg_data.instruction.raw
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_rs1_ready_i
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_rs2_ready_i
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cdb_valid_i
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cdb_except_raised_i
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cdb_rob_idx_i
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cl_reg0_valid_i
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cl_reg0_idx_i
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cl_reg1_valid_i
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cl_reg1_idx_i
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cl_comm_reg_valid_i
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cl_comm_reg_idx_i
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_valid_o
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs1_ready_o
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs1_idx_o
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs1_value_o
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs2_ready_o
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs2_idx_o
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs2_value_o
add wave -noupdate -expand -group ISSUE /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_imm_value_o
add wave -noupdate -group {REGISTER FILE} /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/comm_valid_i
add wave -noupdate -group {REGISTER FILE} /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/comm_rd_idx_i
add wave -noupdate -group {REGISTER FILE} /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/comm_rd_value_i
add wave -noupdate -group {REGISTER FILE} /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/rf_data
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_valid_i
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rd_idx_i
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rob_idx_i
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs1_idx_i
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs2_idx_i
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs1_busy_o
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs1_rob_idx_o
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs2_busy_o
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs2_rob_idx_o
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/comm_valid_i
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/comm_rd_idx_i
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/comm_head_idx_i
add wave -noupdate -expand -group {REGISTER STATUS} /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/regstat_data
add wave -noupdate -group COMMIT /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_valid_i
add wave -noupdate -group COMMIT /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/u_commit_cu/curr_state
add wave -noupdate -group COMMIT /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_data
add wave -noupdate -expand -group CDB -expand /tb_with_l2cemu/u_datapath/u_backend/u_cdb/data_o
add wave -noupdate -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_valid_i
add wave -noupdate -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_instr_i.raw
add wave -noupdate -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_pc_i
add wave -noupdate -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_valid
add wave -noupdate -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_data
add wave -noupdate -expand -group {STORE BUFFER} /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/issue_logic_valid_i
add wave -noupdate -expand -group {STORE BUFFER} -expand -subitemconfig {{/tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_data[0]} -expand} /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_data
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {840 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 99
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 10
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {612 ns} {1021 ns}
