onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_bare/u_datapath/clk_i
add wave -noupdate /tb_bare/u_datapath/rst_n_i
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/mem_flush_o
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/ins_mem_valid_i
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/ins_mem_ready_i
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/ins_mem_valid_o
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/ins_mem_ready_o
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/ins_mem_ans_i
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/ins_mem_req_o
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/data_mem_valid_i
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/data_mem_ready_i
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/data_mem_valid_o
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/data_mem_ready_o
add wave -noupdate -group DATAPATH /tb_bare/u_datapath/data_mem_ans_i
add wave -noupdate -group DATAPATH -expand /tb_bare/u_datapath/data_mem_req_o
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/flush_i
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/flush_bpu_i
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/mem_valid_i
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/mem_ready_i
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/mem_valid_o
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/mem_ready_o
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/mem_ans_i
add wave -noupdate -expand -group {FETCH STAGE} -expand /tb_bare/u_datapath/u_fetch_stage/mem_req_o
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/issue_ready_i
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/issue_valid_o
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/issue_instr_o
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/issue_pred_o
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/issue_except_raised_o
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/issue_except_code_o
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/comm_except_raised_i
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/comm_except_pc_i
add wave -noupdate -expand -group {FETCH STAGE} /tb_bare/u_datapath/u_fetch_stage/comm_res_valid_i
add wave -noupdate -expand -group {FETCH STAGE} -expand /tb_bare/u_datapath/u_fetch_stage/comm_res_i
add wave -noupdate -expand -group {FETCH STAGE} -expand -group {PC GEN} /tb_bare/u_datapath/u_fetch_stage/u_pc_gen/comm_except_raised_i
add wave -noupdate -expand -group {FETCH STAGE} -expand -group {PC GEN} /tb_bare/u_datapath/u_fetch_stage/u_pc_gen/comm_except_pc_i
add wave -noupdate -expand -group {FETCH STAGE} -expand -group {PC GEN} /tb_bare/u_datapath/u_fetch_stage/u_pc_gen/comm_res_valid_i
add wave -noupdate -expand -group {FETCH STAGE} -expand -group {PC GEN} -expand /tb_bare/u_datapath/u_fetch_stage/u_pc_gen/comm_res_i
add wave -noupdate -expand -group {FETCH STAGE} -expand -group {PC GEN} -expand /tb_bare/u_datapath/u_fetch_stage/u_pc_gen/pred_i
add wave -noupdate -expand -group {FETCH STAGE} -expand -group {PC GEN} /tb_bare/u_datapath/u_fetch_stage/u_pc_gen/mem_ready_i
add wave -noupdate -expand -group {FETCH STAGE} -expand -group {PC GEN} /tb_bare/u_datapath/u_fetch_stage/u_pc_gen/valid_o
add wave -noupdate -expand -group {FETCH STAGE} -expand -group {PC GEN} /tb_bare/u_datapath/u_fetch_stage/u_pc_gen/pc_o
add wave -noupdate -expand -group {FETCH STAGE} -expand -group {PC GEN} /tb_bare/u_datapath/u_fetch_stage/u_pc_gen/next_pc
add wave -noupdate -expand -group {FETCH STAGE} -expand -group {PC GEN} /tb_bare/u_datapath/u_fetch_stage/u_pc_gen/add_pc
add wave -noupdate -expand -group {FETCH STAGE} -expand -group {PC GEN} /tb_bare/u_datapath/u_fetch_stage/u_pc_gen/adder_out
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/flush_i
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/valid_i
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/ready_i
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/valid_o
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/ready_o
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/data_i
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/data_o
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/head_cnt
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/tail_cnt
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/head_cnt_en
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/tail_cnt_en
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/head_cnt_clr
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/tail_cnt_clr
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/data
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/data_valid
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/fifo_push
add wave -noupdate -group ISSUE_QUEUE /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_fifo/fifo_pop
add wave -noupdate -group {ISSUE CU} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_cu/flush_i
add wave -noupdate -group {ISSUE CU} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_cu/issue_stall_i
add wave -noupdate -group {ISSUE CU} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_cu/issue_queue_ready_i
add wave -noupdate -group {ISSUE CU} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_cu/comm_resume_i
add wave -noupdate -group {ISSUE CU} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_cu/fetch_ready_o
add wave -noupdate -group {ISSUE CU} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_cu/curr_state
add wave -noupdate -group {ISSUE CU} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_cu/next_state
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/cu_stall_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/iq_valid_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/iq_ready_o
add wave -noupdate -group {ISSUE LOGIC} -expand /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/iq_instr_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_valid_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs1_busy_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs1_rob_idx_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs2_busy_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs2_rob_idx_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rd_idx_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rob_idx_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs1_idx_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs2_idx_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/intrf_rs1_value_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/intrf_rs2_value_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/intrf_rs1_idx_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/intrf_rs2_idx_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_ready_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_valid_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_eu_ctl_o
add wave -noupdate -group {ISSUE LOGIC} -expand /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_rs1_o
add wave -noupdate -group {ISSUE LOGIC} -expand /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_rs2_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_imm_value_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_rob_idx_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_curr_pc_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_pred_target_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_pred_taken_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_ready_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_valid_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_tail_idx_i
add wave -noupdate -group {ISSUE LOGIC} -expand -subitemconfig {/tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_data_o.instruction -expand} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_data_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_jb_instr_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_rs1_rob_idx_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_rs1_ready_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_rs1_value_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_rs2_rob_idx_o
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_rs2_ready_i
add wave -noupdate -group {ISSUE LOGIC} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/comm_rs2_value_i
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/instruction_i
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/except_raised_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/except_code_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/res_ready_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/stall_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/eu_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/eu_ctl_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/fp_rs_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/rs1_req_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/rs1_is_pc_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/rs2_req_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/rs2_is_imm_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/imm_format_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/regstat_upd_o
add wave -noupdate -group {ISSUE LOGIC} -group {ISSUE DECODER} /tb_bare/u_datapath/u_backend/u_issue_stage/u_issue_logic/u_issue_decoder/jb_instr_o
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/flush_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/issue_lb_valid_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/issue_sb_valid_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/issue_lb_ready_o
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/issue_sb_ready_o
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/issue_type_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/issue_rs1_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/issue_rs2_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/issue_imm_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/issue_dest_rob_idx_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/comm_spec_instr_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/comm_rob_head_idx_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_valid_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_lb_ready_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_sb_ready_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_lb_valid_o
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_sb_valid_o
add wave -noupdate -group {LOAD STORE UNIT} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_data_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_lb_data_o
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_sb_data_o
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/mem_valid_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/mem_ready_i
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/mem_valid_o
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/mem_ready_o
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/mem_req_o
add wave -noupdate -group {LOAD STORE UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/mem_ans_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/issue_valid_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/issue_ready_o
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/issue_type_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/issue_rs1_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/issue_imm_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/issue_dest_rob_idx_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_valid_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_ready_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_valid_o
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_data_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_data_o
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/adder_valid_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/adder_ready_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/adder_valid_o
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/adder_ready_o
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/adder_ans_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/adder_req_o
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/mem_valid_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/mem_ready_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/mem_valid_o
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/mem_ready_o
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/mem_req_o
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/mem_ans_i
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} -expand -subitemconfig {{/tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/data[1]} -expand} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/data
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/curr_state
add wave -noupdate -group {LOAD STORE UNIT} -group {LOAD BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/read_data
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/issue_valid_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/issue_ready_o
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/issue_type_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/issue_rs1_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/issue_rs2_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/issue_imm_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/issue_dest_rob_idx_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/comm_spec_instr_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/comm_rob_head_idx_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_valid_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_ready_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_valid_o
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_data_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_data_o
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/adder_valid_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/adder_ready_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/adder_valid_o
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/adder_ready_o
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/adder_ans_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/adder_req_o
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/mem_valid_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/mem_ready_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/mem_valid_o
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/mem_ready_o
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/mem_req_o
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/mem_ans_i
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/head_idx
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/tail_idx
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/addr_idx
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/mem_idx
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/curr_state
add wave -noupdate -group {LOAD STORE UNIT} -group {STORE BUFFER} -expand -subitemconfig {{/tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/data[2]} -expand} /tb_bare/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/data
add wave -noupdate -group {ALU UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/issue_valid_i
add wave -noupdate -group {ALU UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/issue_ready_o
add wave -noupdate -group {ALU UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/issue_eu_ctl_i
add wave -noupdate -group {ALU UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/issue_rs1_i
add wave -noupdate -group {ALU UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/issue_rs2_i
add wave -noupdate -group {ALU UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/issue_dest_rob_idx_i
add wave -noupdate -group {ALU UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_ready_i
add wave -noupdate -group {ALU UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_valid_i
add wave -noupdate -group {ALU UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_valid_o
add wave -noupdate -group {ALU UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_data_i
add wave -noupdate -group {ALU UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_data_o
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/issue_valid_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/issue_ready_o
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/issue_eu_ctl_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/issue_rs1_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/issue_rs2_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/issue_dest_rob_idx_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/cdb_ready_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/cdb_valid_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/cdb_valid_o
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/cdb_data_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/cdb_data_o
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_ready_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_valid_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_valid_o
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_ready_o
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_entry_idx_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_result_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_except_raised_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_except_code_i
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_ctl_o
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_rs1_o
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_rs2_o
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/eu_entry_idx_o
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/data
add wave -noupdate -group {ALU UNIT} -expand -group {ALU RS} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_arith_rs/curr_state
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_valid_i
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_ready_o
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_branch_type_i
add wave -noupdate -group {BRANCH UNIT} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_rs1_i
add wave -noupdate -group {BRANCH UNIT} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_rs2_i
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_imm_value_i
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_dest_rob_idx_i
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_curr_pc_i
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_pred_target_i
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_pred_taken_i
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/cdb_ready_i
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/cdb_valid_i
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/cdb_valid_o
add wave -noupdate -group {BRANCH UNIT} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/cdb_data_i
add wave -noupdate -group {BRANCH UNIT} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/cdb_data_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/issue_valid_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/issue_ready_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/issue_branch_type_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/issue_rs1_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/issue_rs2_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/issue_imm_value_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/issue_dest_rob_idx_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/issue_curr_pc_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/issue_pred_target_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/issue_pred_taken_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/cdb_ready_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/cdb_valid_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/cdb_valid_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/cdb_data_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/cdb_data_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_valid_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_ready_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_valid_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_ready_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_entry_idx_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_res_mis_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_res_taken_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_res_target_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_except_raised_i
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_entry_idx_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_rs1_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_rs2_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_imm_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_curr_pc_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_pred_target_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_pred_taken_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/bu_branch_type_o
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} -expand -subitemconfig {{/tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/data[0]} -expand} /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/data
add wave -noupdate -group {BRANCH UNIT} -expand -group {BRANCH RS} -expand /tb_bare/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/curr_state
add wave -noupdate -group CDB /tb_bare/u_datapath/u_backend/u_cdb/max_prio_valid_i
add wave -noupdate -group CDB /tb_bare/u_datapath/u_backend/u_cdb/max_prio_ready_o
add wave -noupdate -group CDB /tb_bare/u_datapath/u_backend/u_cdb/max_prio_data_i
add wave -noupdate -group CDB /tb_bare/u_datapath/u_backend/u_cdb/rs_valid_i
add wave -noupdate -group CDB /tb_bare/u_datapath/u_backend/u_cdb/rs_ready_o
add wave -noupdate -group CDB /tb_bare/u_datapath/u_backend/u_cdb/rs_data_i
add wave -noupdate -group CDB /tb_bare/u_datapath/u_backend/u_cdb/rob_ready_i
add wave -noupdate -group CDB /tb_bare/u_datapath/u_backend/u_cdb/valid_o
add wave -noupdate -group CDB /tb_bare/u_datapath/u_backend/u_cdb/data_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/mis_flush_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/fe_bpu_flush_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/fe_res_valid_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand /tb_bare/u_datapath/u_backend/u_commit_stage/fe_res_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/fe_except_raised_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/fe_except_pc_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_valid_i
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_ready_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_data_i
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_jb_instr_i
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_tail_idx_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_rs1_rob_idx_i
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_rs1_ready_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_rs1_value_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_rs2_rob_idx_i
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_rs2_ready_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_rs2_value_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/issue_resume_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/cdb_valid_i
add wave -noupdate -expand -group {COMMIT STAGE} -expand /tb_bare/u_datapath/u_backend/u_commit_stage/cdb_data_i
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/cdb_ready_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/sb_spec_instr_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/sb_rob_head_idx_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/int_rs_valid_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/int_rf_valid_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/rs_head_idx_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/rd_idx_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/rd_value_o
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/inreg_cu_valid
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/inreg_data_out
add wave -noupdate -expand -group {COMMIT STAGE} /tb_bare/u_datapath/u_backend/u_commit_stage/comm_reg_valid
add wave -noupdate -expand -group {COMMIT STAGE} -expand -subitemconfig {/tb_bare/u_datapath/u_backend/u_commit_stage/comm_reg_data.data -expand /tb_bare/u_datapath/u_backend/u_commit_stage/comm_reg_data.data.instruction -expand} /tb_bare/u_datapath/u_backend/u_commit_stage/comm_reg_data
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/flush_i
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/issue_valid_i
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/issue_ready_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/issue_data_i
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/issue_tail_idx_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/issue_rs1_rob_idx_i
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/issue_rs2_rob_idx_i
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/opfwd_rs1_valid_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/opfwd_rs1_ready_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/opfwd_rs1_value_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/opfwd_rs2_valid_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/opfwd_rs2_ready_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/opfwd_rs2_value_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/comm_valid_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/comm_ready_i
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/comm_data_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/comm_head_idx_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/cdb_valid_i
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/cdb_data_i
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/cdb_ready_o
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB -expand /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/data_valid
add wave -noupdate -expand -group {COMMIT STAGE} -group ROB -expand /tb_bare/u_datapath/u_backend/u_commit_stage/u_rob/data
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/comm_type_i
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/mispredict_i
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/comm_reg_en_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/comm_reg_clr_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/jb_instr_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/valid_i
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/ready_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/instr_i
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/res_ready_i
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/except_raised_i
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/except_code_i
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/int_rs_valid_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/int_rf_valid_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/sb_exec_store_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/csr_valid_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/csr_type_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/fe_ready_i
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/fe_res_valid_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/fe_bpu_flush_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/mis_flush_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/issue_resume_o
add wave -noupdate -expand -group {COMMIT STAGE} -expand -group {COMMIT CU} /tb_bare/u_datapath/u_backend/u_commit_stage/u_commit_cu/curr_state
add wave -noupdate -expand -group {COMMIT STAGE} -group {to CSRs} /tb_bare/u_datapath/u_backend/u_commit_stage/csr_valid_o
add wave -noupdate -expand -group {COMMIT STAGE} -group {to CSRs} /tb_bare/u_datapath/u_backend/u_commit_stage/csr_ready_i
add wave -noupdate -expand -group {COMMIT STAGE} -group {to CSRs} /tb_bare/u_datapath/u_backend/u_commit_stage/csr_data_i
add wave -noupdate -expand -group {COMMIT STAGE} -group {to CSRs} /tb_bare/u_datapath/u_backend/u_commit_stage/csr_acc_exc_i
add wave -noupdate -expand -group {COMMIT STAGE} -group {to CSRs} /tb_bare/u_datapath/u_backend/u_commit_stage/csr_instr_type_o
add wave -noupdate -expand -group {COMMIT STAGE} -group {to CSRs} /tb_bare/u_datapath/u_backend/u_commit_stage/csr_funct3_o
add wave -noupdate -expand -group {COMMIT STAGE} -group {to CSRs} /tb_bare/u_datapath/u_backend/u_commit_stage/csr_addr_o
add wave -noupdate -expand -group {COMMIT STAGE} -group {to CSRs} /tb_bare/u_datapath/u_backend/u_commit_stage/csr_rs1_idx_o
add wave -noupdate -expand -group {COMMIT STAGE} -group {to CSRs} /tb_bare/u_datapath/u_backend/u_commit_stage/csr_rs1_value_o
add wave -noupdate -expand -group {COMMIT STAGE} -group {to CSRs} /tb_bare/u_datapath/u_backend/u_commit_stage/csr_except_code_o
add wave -noupdate -expand -group {COMMIT STAGE} -group {to CSRs} /tb_bare/u_datapath/u_backend/u_commit_stage/csr_rd_idx_o
add wave -noupdate -expand -group {REGISTER FILE} /tb_bare/u_datapath/u_backend/u_int_rf/clk_i
add wave -noupdate -expand -group {REGISTER FILE} /tb_bare/u_datapath/u_backend/u_int_rf/rst_n_i
add wave -noupdate -expand -group {REGISTER FILE} /tb_bare/u_datapath/u_backend/u_int_rf/comm_valid_i
add wave -noupdate -expand -group {REGISTER FILE} /tb_bare/u_datapath/u_backend/u_int_rf/comm_rd_idx_i
add wave -noupdate -expand -group {REGISTER FILE} /tb_bare/u_datapath/u_backend/u_int_rf/comm_rd_value_i
add wave -noupdate -expand -group {REGISTER FILE} /tb_bare/u_datapath/u_backend/u_int_rf/issue_rs1_idx_i
add wave -noupdate -expand -group {REGISTER FILE} /tb_bare/u_datapath/u_backend/u_int_rf/issue_rs2_idx_i
add wave -noupdate -expand -group {REGISTER FILE} /tb_bare/u_datapath/u_backend/u_int_rf/issue_rs1_value_o
add wave -noupdate -expand -group {REGISTER FILE} /tb_bare/u_datapath/u_backend/u_int_rf/issue_rs2_value_o
add wave -noupdate -expand -group {REGISTER FILE} -radix decimal -childformat {{{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[1]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[2]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[3]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[4]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[5]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[6]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[7]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[8]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[9]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[10]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[11]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[12]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[13]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[14]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[15]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[16]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[17]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[18]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[19]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[20]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[21]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[22]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[23]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[24]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[25]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[26]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[27]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[28]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[29]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[30]} -radix decimal} {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[31]} -radix decimal}} -expand -subitemconfig {{/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[1]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[2]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[3]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[4]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[5]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[6]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[7]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[8]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[9]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[10]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[11]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[12]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[13]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[14]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[15]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[16]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[17]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[18]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[19]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[20]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[21]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[22]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[23]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[24]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[25]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[26]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[27]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[28]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[29]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[30]} {-height 17 -radix decimal} {/tb_bare/u_datapath/u_backend/u_int_rf/rf_data[31]} {-height 17 -radix decimal}} /tb_bare/u_datapath/u_backend/u_int_rf/rf_data
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/clk_i
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/rst_n_i
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/flush_i
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/issue_valid_i
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/issue_rd_idx_i
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/issue_rob_idx_i
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/issue_rs1_idx_i
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/issue_rs2_idx_i
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/issue_rs1_busy_o
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/issue_rs1_rob_idx_o
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/issue_rs2_busy_o
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/issue_rs2_rob_idx_o
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/comm_valid_i
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/comm_rd_idx_i
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/comm_head_idx_i
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/busy_rob_idx_upd
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/busy_rob_idx
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/skip_cnt_upd
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/busy_cnt_en
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/busy_cnt_up
add wave -noupdate -group {INT REGSTAT} /tb_bare/u_datapath/u_backend/u_int_regstat/busy_cnt_clr
add wave -noupdate -group {INT REGSTAT} -expand /tb_bare/u_datapath/u_backend/u_int_regstat/busy_cnt
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/flush_i
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/ins_valid_i
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/ins_ready_i
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/ins_valid_o
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/ins_ready_o
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/ins_req_i
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/ins_ans_o
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/data_valid_i
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/data_ready_i
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/data_valid_o
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/data_ready_o
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/data_req_i
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/data_ans_o
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/ins_pipe_valid
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/data_pipe_valid
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/ins_pipe_reg
add wave -noupdate -group {MEM EMU} /tb_bare/u_memory_bare_emu/data_pipe_reg
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {4450 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 197
configure wave -valuecolwidth 154
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
WaveRestoreZoom {3905 ns} {4995 ns}
