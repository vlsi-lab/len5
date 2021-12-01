onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_with_l2cemu/clk
add wave -noupdate /tb_with_l2cemu/rst_n
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/clk_i
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/rst_n_i
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/fe_ins_i
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/fe_except_raised_i
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/be_stall_i
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/be_flush_i
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/stall_o
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/flush_o
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/mem_l2c_update_done
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/mem_flush_o
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/mem_abort_o
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/mem_clr_l1tlb_mshr
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/mem_clr_l2tlb_mshr
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/mem_clear_dmshr_dregs
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/mem_synch_l1dc_l2c
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/mem_L1TLB_flush_type
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/mem_L2TLB_flush_type
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/mem_flush_asid
add wave -noupdate -group MAIN_CU /tb_with_l2cemu/u_datapath/u_main_cu/mem_flush_page
add wave -noupdate -expand -group DATAPATH -group PORTS /tb_with_l2cemu/u_datapath/clk_i
add wave -noupdate -expand -group DATAPATH -group PORTS /tb_with_l2cemu/u_datapath/rst_n_i
add wave -noupdate -expand -group DATAPATH -group PORTS /tb_with_l2cemu/u_datapath/l2c_l2arb_req_rdy_i
add wave -noupdate -expand -group DATAPATH -group PORTS /tb_with_l2cemu/u_datapath/l2c_l2arb_ans_i
add wave -noupdate -expand -group DATAPATH -group PORTS /tb_with_l2cemu/u_datapath/l2arb_l2c_req_o
add wave -noupdate -expand -group DATAPATH -group PORTS /tb_with_l2cemu/u_datapath/l2arb_l2c_ans_rdy_o
add wave -noupdate -expand -group DATAPATH -group PORTS /tb_with_l2cemu/u_datapath/l2c_flush_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/clk_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/rst_n_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/flush_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/addr_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/addr_valid_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/addr_ready_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/data_ready_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/icache_frontend_ans_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/issue_ready_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/issue_valid_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/instruction_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/curr_pc_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/pred_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/res_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/except_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/except_code_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/except_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/except_pc_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/rst_n_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/flush_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/pc_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/fetch_ready_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/addr_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/addr_valid_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/addr_ready_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/data_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/data_valid_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/data_ready_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/issue_ready_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/issue_valid_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/instruction_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/curr_pc_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/pred_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/icache_frontend_ans_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/except_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/except_code_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/res_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/clk_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/clk_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/rst_n_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/flush_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/pc_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/read_req_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/cache_out_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/read_done_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/addr_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/addr_valid_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/addr_ready_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/data_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/data_valid_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group ICACHE_IF /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_icache_ifc/data_ready_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/clk_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/rst_n_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/flush_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/pc_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/fetch_ready_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/cache_out_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/read_done_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/read_req_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/icache_frontend_ans_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/except_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/except_code_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/issue_ready_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/issue_valid_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/instruction_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group IFU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_ifu/curr_pc_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group BPU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_bpu/clk_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group BPU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_bpu/rst_n_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group BPU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_bpu/flush_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group BPU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_bpu/pc_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group BPU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_bpu/res_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group FETCH_STAGE -group BPU /tb_with_l2cemu/u_datapath/u_frontend/fetch_stage_u/u_bpu/pred_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/rst_n_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/clk_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/except_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/except_pc_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/res_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/pred_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/fetch_ready_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/pc_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_PRIORITY_ENC /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/clk_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_PRIORITY_ENC /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/rst_n_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_PRIORITY_ENC /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/except_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_PRIORITY_ENC /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/except_pc_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_PRIORITY_ENC /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/res_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_PRIORITY_ENC /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/pred_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_PRIORITY_ENC /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/fetch_ready_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_PRIORITY_ENC /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/pc_o
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_REG /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/clk_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_REG /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/rst_n_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_REG /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/except_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_REG /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/except_pc_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_REG /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/res_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_REG /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/pred_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_REG /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/fetch_ready_i
add wave -noupdate -expand -group DATAPATH -group FRONTEND -group PC_GEN_STAGE -group PC_REG /tb_with_l2cemu/u_datapath/u_frontend/pc_gen_stage_u/pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/main_cu_stall_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/main_cu_flush_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_curr_pc_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_instr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_pred_target_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_pred_taken_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_except_raised_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_except_code_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_res_pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_res_target_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_res_taken_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_res_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_res_mispredict_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_except_raised_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/fetch_except_pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/dtlb_ans_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/dtlb_wup_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/dtlb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/dtlb_req_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/dcache_ans_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/dcache_wup_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/dcache_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/dcache_req_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/mem_vmem_on_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/mem_sum_bit_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/mem_mxr_bit_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/mem_priv_mode_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/mem_priv_mode_ls_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/mem_base_asid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group PORTS /tb_with_l2cemu/u_datapath/u_backend/mem_csr_root_ppn_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/main_cu_stall_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/fetch_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/fetch_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/fetch_curr_pc_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/fetch_instr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/fetch_pred_target_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/fetch_pred_taken_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/fetch_except_raised_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/fetch_except_code_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/int_regstat_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/int_regstat_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/int_regstat_rs1_busy_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/int_regstat_rs1_rob_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/int_regstat_rs2_busy_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/int_regstat_rs2_rob_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/int_regstat_rd_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/int_regstat_rob_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/int_regstat_rs1_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/int_regstat_rs2_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/intrf_rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/intrf_rs2_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/intrf_rs1_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/intrf_rs2_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_eu_ctl_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs1_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs1_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs1_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs2_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs2_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rs2_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_imm_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_rob_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_pred_pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_pred_target_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/ex_pred_taken_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/cdb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/cdb_except_raised_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/cdb_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/cdb_rob_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_rs1_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_rs2_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_rs2_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_tail_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_rs1_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_rs2_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_instr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_rd_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_except_raised_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_except_code_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_except_aux_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_res_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/rob_res_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/iq_il_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/il_iq_ready
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/iq_il_curr_pc
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/iq_il_instr
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/iq_il_pred_target
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/iq_il_pred_taken
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/iq_il_except_raised
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/iq_il_except_code
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/main_cu_stall_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/iq_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/iq_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/iq_curr_pc_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/iq_instruction_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/iq_pred_target_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/iq_pred_taken_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/iq_except_raised_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/iq_except_code_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs1_busy_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs1_rob_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs2_busy_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs2_rob_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rd_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rob_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs1_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/int_regstat_rs2_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/intrf_rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/intrf_rs2_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/intrf_rs1_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/intrf_rs2_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_eu_ctl_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_rs1_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_rs1_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_rs1_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_rs2_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_rs2_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_rs2_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_imm_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_rob_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_pred_pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_pred_target_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/ex_pred_taken_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cdb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cdb_except_raised_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cdb_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/cdb_rob_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_rs1_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_rs2_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_rs2_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_tail_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_rs1_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_rs2_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_instr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_rd_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_except_raised_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_except_code_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_except_aux_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_res_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_res_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/instr_rs1_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/instr_rs2_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/instr_rd_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/instr_imm_i_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/instr_imm_s_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/instr_imm_b_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/instr_imm_u_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/instr_imm_j_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/instr_imm_rs1_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/imm_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_tail_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/regstat_ready
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_rs1_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rob_rs2_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rs1_ready
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rs2_ready
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rs1_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/rs2_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_except_raised
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_except_code
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_res_ready
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_stall_possible
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_assigned_eu
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_eu_ctl
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_rs1_req
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_rs1_is_pc
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_rs2_req
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_rs2_is_imm
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_imm_format
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_regstat_upd
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/eh_stall_possible
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/eh_except_raised
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/eh_except_code
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/eh_except_aux
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ISSUE_STAGE -group ISSUE_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_issue_stage/u_issue_logic/id_fp_rs
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rd_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rob_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs1_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs2_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs1_busy_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs1_rob_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs2_busy_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/issue_rs2_rob_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/comm_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/comm_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/comm_rd_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/comm_head_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/regstat_issue_upd
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group INT_REGSTAT /tb_with_l2cemu/u_datapath/u_backend/u_int_regstat/regstat_comm_upd
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -expand -group INT_RF /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -expand -group INT_RF /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -expand -group INT_RF /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/rf_data
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -expand -group INT_RF /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/comm_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -expand -group INT_RF /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/comm_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -expand -group INT_RF /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/comm_rd_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -expand -group INT_RF /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/comm_rd_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -expand -group INT_RF /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/issue_rs1_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -expand -group INT_RF /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/issue_rs2_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -expand -group INT_RF /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/issue_rs1_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -expand -group INT_RF /tb_with_l2cemu/u_datapath/u_backend/u_int_rf/issue_rs2_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/fetch_res_pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/fetch_res_target_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/fetch_res_taken_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/fetch_res_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/fetch_res_mispredict_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_eu_ctl_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_rs1_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_rs1_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_rs2_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_rs2_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_rs2_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_imm_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_rob_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_pred_pc_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_pred_target_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/issue_pred_taken_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/cdb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/cdb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/cdb_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/cdb_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/cdb_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/rob_head_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/cl_store_committing_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/vm_mode_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/dtlb_ans_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/dtlb_wup_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/dtlb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/dtlb_req_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/dcache_ans_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/dcache_wup_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/dcache_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/dcache_req_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/vm_mode_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/issue_lb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/issue_sb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/lb_issue_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/sb_issue_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/ldst_type_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/rs1_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/rs1_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/rs2_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/rs2_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/rs2_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/imm_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/dest_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/dtlb_ans_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/dtlb_wup_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/dtlb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/dtlb_req_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/dcache_ans_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/dcache_wup_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/dcache_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/dcache_req_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/rob_head_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cl_store_committing_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_lb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_sb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_lb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_sb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/lb_cdb_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/sb_cdb_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/cdb_lsb_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/lb_cdb_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group PORTS /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/sb_cdb_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vm_mode_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/issue_logic_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/issue_logic_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/load_type_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/rs1_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/rs1_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/imm_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dest_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_vaddr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_except_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_isstore_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/rs1_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/imm_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_ldtype_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_wu_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_ans_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_vaddr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_ppn_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_except_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_isstore_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_vaddr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_wu_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_ans_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_lineaddr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_isstore_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_paddr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/inflight_store_cnt_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/store_committing_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vfwd_hit_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vfwd_depfree_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/pfwd_hit_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/pfwd_depfree_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vfwd_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/pfwd_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vfwd_vaddr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/pfwd_paddr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vfwd_ldtype_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/pfwd_ldtype_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vfwd_older_stores_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/pfwd_older_stores_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_except_raised_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_except_raised_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_except_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/new_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_req_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_req_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_req_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_req_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/new_idx_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vadder_idx_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dtlb_idx_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_idx_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/cdb_idx_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vfwd_idx_reg_en
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vfwd_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/pfwd_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/pfwd_idx_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/lb_insert
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/lb_vadder_req
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/lb_vadder_ans
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/lb_dtlb_req
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/lb_dtlb_wu
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/lb_dtlb_ans
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/lb_dcache_req
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/lb_dcache_wu
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/lb_dcache_ans
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/lb_pop
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vfwd_req
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/pfwd_req
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/dcache_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/valid_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/busy_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/store_dep_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/pfwd_attempted_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/no_older_stores_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/rs1_ready_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/vaddr_ready_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/paddr_ready_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/except_raised_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/completed_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group LOAD_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_load_buffer/lb_data
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vm_mode_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/issue_logic_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/issue_logic_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/store_type_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/rs1_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/rs1_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/rs2_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/rs2_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/rs2_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/imm_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dest_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_vaddr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_except_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_isstore_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/rs1_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/imm_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_sttype_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_wu_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_ans_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_vaddr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_ppn_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_except_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_isstore_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_vaddr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_wu_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_ans_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_lineaddr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_isstore_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_paddr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dcache_sttype_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vfwd_vaddr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/pfwd_paddr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vfwd_ldtype_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/pfwd_ldtype_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vfwd_older_stores_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/pfwd_older_stores_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/inflight_store_cnt_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/lb_store_committing_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vfwd_hit_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vfwd_depfree_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/pfwd_hit_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/pfwd_depfree_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vfwd_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/pfwd_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/rob_head_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cl_store_committing_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_except_raised_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_except_raised_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_except_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_head_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_tail_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_req_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_req_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_req_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vadder_idx_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dtlb_idx_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/cdb_idx_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/head_cnt_en
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/head_cnt_clr
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/tail_cnt_en
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/tail_cnt_clr
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/inflight_count
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_push
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_pop
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_vadder_req
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_vadder_ans
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_dtlb_req
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_dtlb_wu
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_dtlb_ans
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_dcache_req
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_dcache_wu
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_dcache_ans
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_cdb_req
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_store_committing
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/valid_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/busy_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/rs1_ready_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vaddr_ready_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/paddr_ready_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/dc_completed_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/except_raised_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/completed_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vfwd_allowed
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vfwd_hit
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vfwd_depfree
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/vfwd_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/pfwd_allowed
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/pfwd_hit
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/pfwd_depfree
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/pfwd_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group STORE_BUFFER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_store_buffer/sb_data
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/vm_mode_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/lsb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/lsb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/lsb_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/lsb_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/is_store_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/imm_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/lsb_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/ldst_type_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/is_store_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/vaddr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/lsb_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/except_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/rs1_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/imm_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/ldst_type
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/vm_mode
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/align_except
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/pfault_except
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group LOAD_STORE_UNIT -group VADDR_ADDER /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_load_store_unit/u_vaddr_adder/vm_mode_e
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/issue_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/branch_type_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs1_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs1_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs2_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs2_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs2_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/imm_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/dest_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/pred_pc_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/pred_target_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/pred_taken_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/res_pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/res_target_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/res_taken_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/res_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/res_mispredict_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/cdb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/cdb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/cdb_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/cdb_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/cdb_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs_bu_rs1
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs_bu_rs2
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs_bu_imm
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs_bu_pred_pc
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs_bu_pred_target
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs_bu_pred_taken
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs_bu_branch_type
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/bu_rs_res_mispredict
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/bu_rs_ready
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/bu_rs_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs_bu_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/rs_bu_ready
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group BRANCH_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_branch_unit/u_branch_rs/rs_data
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/issue_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/issue_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/eu_ctl_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs1_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs1_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs2_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs2_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs2_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/dest_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_except_raised_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_except_raised_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/cdb_except_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs_alu_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs_alu_ready
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/alu_rs_valid
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/alu_rs_ready
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs_alu_entry_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs_alu_ctl
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs_alu_rs1_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/rs_alu_rs2_value
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/alu_rs_entry_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/alu_rs_result
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/alu_rs_except_raised
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/alu_rs_except_code
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group ALU_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_alu_unit/u_alu_generic_rs/rs_data
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/issue_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/issue_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/rs1_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/rs1_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/dest_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/cdb_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/cdb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/cdb_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/cdb_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/cdb_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group EXEC_STAGE -group OP_ONLY_UNIT /tb_with_l2cemu/u_datapath/u_backend/u_exec_stage/u_op_only_unit/u_op_only_rs/rs_data
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/max_prio_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/max_prio_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/max_prio_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/rs_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/rs_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/rs_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/rob_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/rob_valid_k
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/low_prio_mux_data
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/served_max_prio
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/served
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/rs_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CDB /tb_with_l2cemu/u_datapath/u_backend/u_cdb/max_prio_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/flush_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_rs1_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_rs1_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_rs1_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_rs2_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_rs2_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_rs2_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_instr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_pc_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_rd_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_except_raised_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_except_code_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_except_aux_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_res_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_res_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/issue_tail_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/cdb_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/cdb_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/cdb_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/comm_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/comm_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/comm_instr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/comm_pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/comm_rd_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/comm_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/comm_except_raised_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/comm_except_code_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/comm_head_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/sb_head_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_head_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_tail_idx
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_tail_en1
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_head_en
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_head_clr
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_tail_en
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_tail_clr
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_push
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_pop
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_wr_res
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/valid_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/res_ready_a
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/comm_except_code_test
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group ROB /tb_with_l2cemu/u_datapath/u_backend/u_rob/rob_data
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/main_cu_flush_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/fe_except_raised_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/fe_except_pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_instr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_pc_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_rd_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_except_raised_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_except_code_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_head_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/sb_store_committing_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/int_rs_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/int_rs_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/int_rf_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/int_rf_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rs_head_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rd_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rd_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_acc_exc_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_instr_type_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_funct3_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_addr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_rs1_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_rs1_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_except_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_rd_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/cd_comm_possible
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/eh_no_except
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/instr_opcode
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/sb_store_committing_t
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/mispredict
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/main_cu_flush_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/fe_except_raised_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/fe_except_pc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_instr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_pc_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_rd_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_except_raised_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_except_code_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rob_head_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/sb_store_committing_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/int_rs_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/int_rs_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/int_rf_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/int_rf_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rs_head_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rd_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/rd_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_valid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_ready_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_acc_exc_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_instr_type_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_funct3_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_addr_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_rs1_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_rs1_value_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_except_data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/csr_rd_idx_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/cd_comm_possible
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/eh_no_except
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/instr_opcode
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/sb_store_committing_t
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group COMMIT_LOGIC -group COMMIT_CONTROL_LOGIC /tb_with_l2cemu/u_datapath/u_backend/u_commit_stage/mispredict
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/clk_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/rst_n_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/valid_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/ready_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/instr_type_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/funct3_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/addr_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/rs1_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/rs1_value_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/exc_data_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/rd_idx_i
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/data_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/acc_exc_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/vm_mode_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/mem_vmem_on_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/mem_sum_bit_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/mem_mxr_bit_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/mem_priv_mode_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/mem_priv_mode_ls_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/mem_base_asid_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/mem_csr_root_ppn_o
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/csr_rd_val
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/uimm_zext
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/inv_acc_exc
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/inv_op_exc
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/priv_mode
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/satp
add wave -noupdate -expand -group DATAPATH -expand -group BACKEND -group CSRS /tb_with_l2cemu/u_datapath/u_backend/u_csrs/mstatus
add wave -noupdate -group L2C_EMU /tb_with_l2cemu/u_cache_L2_system_emulator/flush_i
add wave -noupdate -group L2C_EMU /tb_with_l2cemu/u_cache_L2_system_emulator/l2arb_l2c_req_i
add wave -noupdate -group L2C_EMU /tb_with_l2cemu/u_cache_L2_system_emulator/l2c_l2arb_req_rdy_o
add wave -noupdate -group L2C_EMU /tb_with_l2cemu/u_cache_L2_system_emulator/l2c_l2arb_ans_o
add wave -noupdate -group L2C_EMU /tb_with_l2cemu/u_cache_L2_system_emulator/l2arb_l2c_ans_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/flush_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/abort_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/clr_l1tlb_mshr_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/clr_l2tlb_mshr_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/clear_dmshr_dregs_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/synch_l1dc_l2c_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/l2c_update_done_o
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/vmem_on_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/sum_bit_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/mxr_bit_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/priv_mode_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/priv_mode_ls_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/base_asid_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/csr_root_ppn_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/L1TLB_flush_type_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/L2TLB_flush_type_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/flush_asid_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/flush_page_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/frontend_icache_req_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/icache_frontend_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/icache_frontend_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/lsq_dtlb_req_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/dtlb_lsq_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/dtlb_lsq_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/dtlb_lsq_wup_o
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/lsq_l1dc_req_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/l1dc_lsq_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/l1dc_lsq_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/l1dc_lsq_wup_o
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/l2arb_l2c_req_o
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/l2c_l2arb_req_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/l2c_l2arb_ans_i
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/l2arb_l2c_ans_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/synch_l1dc_l2c_i
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/en_cnt_i
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/wbb_empty_i
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/upd_l1dc_req_o
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/l2c_update_done_o
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/state_d
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/state_q
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/cnt
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/synch
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/valid
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/done
add wave -noupdate -group MEMORY_SYSTEM -group UPDATEL2_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_updateL2_block/tc
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l1dc_l2arb_req_i
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/icache_l2arb_req_i
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/ptw_l2arb_req_i
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l2arb_l2c_req_o
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l2c_l2arb_req_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l2arb_l1dc_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l2arb_icache_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l2arb_ptw_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l2c_l2arb_ans_i
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l2arb_l1dc_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l2arb_icache_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l2arb_ptw_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l1dc_l2c_ans_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/icache_l2c_ans_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/ptw_l2c_ans_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/l2arb_l2c_ans_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/ans_destination
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/req_sender
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/i_d_priority
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/i_d_winner
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/i_d_winner_valid
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/cache_ptw_priority
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/cache_ptw_winner
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/i_d_tie
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/cache_ptw_tie
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/i_d_priority_update
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/cache_ptw_priority_update
add wave -noupdate -group MEMORY_SYSTEM -group L2C_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_l2c_arbiter/paddr_zero_filling
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/clr_i
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/rst_l1dc_req_i
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/upd_l1dc_req_i
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/en_cnt_o
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/wbb_empty_o
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/lsq_l1dc_req_i
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/l1dc_lsq_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/l1dc_lsq_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/l1dc_lsq_wup_o
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/l1dc_l2c_req_o
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/l2c_l1dc_req_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/l2c_l1dc_ans_i
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/l1dc_l2c_ans_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/dcache_addr
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/tmem_ctrl_vec
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/dmem_ctrl_vec
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/dcache_wtvd
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_L1_SYSTEM /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_L1_system/dcache_wdata
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_RST_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_rst_block/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_RST_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_rst_block/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_RST_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_rst_block/rst_l1dc_req_o
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_RST_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_rst_block/state_d
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_RST_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_rst_block/state_q
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_RST_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_rst_block/cnt
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_RST_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_rst_block/en_cnt
add wave -noupdate -group MEMORY_SYSTEM -group DCACHE_RST_BLOCK /tb_with_l2cemu/u_datapath/u_memory_system/i_dcache_rst_block/tc
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/flush_i
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/abort_i
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/ireq_i
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/ready_o
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/iresp_o
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/tlb_areq_o
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/tlb_ready_i
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/tlb_aresp_i
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/l2_req_o
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/l2_ready
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/l2_resp_i
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/mem_ctrl
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/cache_addr
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/vtag_vec_in
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/vtag_vec_out
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/data_vec_out
add wave -noupdate -group MEMORY_SYSTEM -group ICACHE_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_icache_L1/mem_out
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/ptw_mmuc_req_i
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/ptw_mmuc_write_i
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/mmuc_flush_i
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/mmuc_ptw_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/req_valid
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/wtag
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/wdata
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/wpartial
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/wr_part_en
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/which_side
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/wr_en
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/try_update
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/dec_waddr
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/tag_vec
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/data_vec
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/partial_vec
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/valid_vec
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/comp_tag
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/selected_ppns
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/selected_ppns_idx
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/hit_d
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/hit_q
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/full_hit
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/hit_vec_d
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/hit_vec_q
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/replace_vec_d
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/replace_vec_q
add wave -noupdate -group MEMORY_SYSTEM -group MMU_CACHE /tb_with_l2cemu/u_datapath/u_memory_system/i_mmu_cache/update_replace_vec
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/flush_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/tlb_ptw_req_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_tlb_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_tlb_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/tlb_ptw_ans_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_mmuc_req_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_mmuc_write_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/mmuc_flush_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/mmuc_ptw_ans_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_l2c_req_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/l2c_ptw_req_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/l2c_ptw_ans_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_l2c_ans_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PORTS /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/csr_root_ppn_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/tlb_ptw_req_valid_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/tlb_ptw_ans_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/l2c_ptw_req_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/l2c_ptw_ans_valid_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/ptw_done_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/ptw_tlb_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/load_cnt_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/ptw_mmuc_req_valid_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/mux_rx_sel_internal_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/reg_tx_cond_en_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/reg_ans_cond_en_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/chk_en_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/mmuc_update_cond_en_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/ptw_l2c_req_valid_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/ptw_l2c_ans_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/reg_rx_cond_en_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/cnt_cond_en_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/ptw_tlb_ans_valid_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/state_d
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTW_CU /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/ptw_cu_i/state_q
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTE_CHECKER /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/pte_checker_i/pte_level_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTE_CHECKER /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/pte_checker_i/ppn_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTE_CHECKER /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/pte_checker_i/pte_ctrl_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTE_CHECKER /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/pte_checker_i/chk_en_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTE_CHECKER /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/pte_checker_i/exception_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group PTE_CHECKER /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/pte_checker_i/done_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group MMU_UPDATE_CONTROL /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/mmuc_update_ctrl_i/pte_level_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group MMU_UPDATE_CONTROL /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/mmuc_update_ctrl_i/mmuc_update_cond_en_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group MMU_UPDATE_CONTROL /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/mmuc_update_ctrl_i/ptw_done_i
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group MMU_UPDATE_CONTROL /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/mmuc_update_ctrl_i/wr_en_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group MMU_UPDATE_CONTROL /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/mmuc_update_ctrl_i/which_side_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group MMU_UPDATE_CONTROL /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/mmuc_update_ctrl_i/wr_partial_o
add wave -noupdate -group MEMORY_SYSTEM -group PTW -group MMU_UPDATE_CONTROL /tb_with_l2cemu/u_datapath/u_memory_system/i_ptw/mmuc_update_ctrl_i/partial_o
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/clr_mshr_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/abort_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/sum_bit_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/mxr_bit_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/priv_mode_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/priv_mode_ls_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/base_asid_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/flush_type_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/flush_asid_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/flush_page_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/l1tlb_l2tlb_req_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/l2tlb_l1tlb_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/l2tlb_ptw_req_o
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/ptw_l2tlb_req_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/ptw_l2tlb_ans_i
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/l2tlb_ptw_ans_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/l2tlb_l1tlb_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/tlb_addr
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/tlb_input_entry_tag
add wave -noupdate -group MEMORY_SYSTEM -group L2_TLB /tb_with_l2cemu/u_datapath/u_memory_system/i_l2_tlb/tlb_input_entry_data
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/itlb_l2tlb_req_i
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/dtlb_l2tlb_req_i
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/l1tlb_l2tlb_req_o
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/l2tlb_l1tlb_req_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/l2tlb_itlb_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/l2tlb_dtlb_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/l2tlb_l1tlb_ans_i
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/l2tlb_itlb_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/l2tlb_dtlb_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/itlb_l2tlb_ans_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/dtlb_l2tlb_ans_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/l1tlb_l2tlb_ans_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/req_winner
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/tie_winner
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/is_tie
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/valid_transaction
add wave -noupdate -group MEMORY_SYSTEM -group TLB_ARBITER /tb_with_l2cemu/u_datapath/u_memory_system/i_tlb_arbiter/resolved_tie
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/clr_mshr_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/sum_bit_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/mxr_bit_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/priv_mode_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/base_asid_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/flush_type_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/flush_asid_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/flush_page_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/lsq_dtlb_req_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/dtlb_lsq_req_rdy_o
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/dtlb_lsq_ans_o
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/dtlb_lsq_wup_o
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/dtlb_l2tlb_req_o
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/l2tlb_dtlb_req_rdy_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/l2tlb_dtlb_ans_i
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/valid_tlb_read
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/tlb_valid_vec
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/replace_vec
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/tlb_hit
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/hit_vec
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/hit_idx
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/dtlb_ctrl
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/flush_vec
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/add_mshr_entry
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/put_mshr_entry_wait
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/rm_mshr_entry
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/replace_entry
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/exception_dtlb
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/exception_l2tlb
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/mshr_vpn_to_be_compared
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/mshr_valid_vec
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/mshr_valid_not_waiting_vec
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/mshr_oh_valid_not_waiting_vec
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/mshr_valid_not_waiting_idx
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/mshr_oh_invalid_vec
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/mshr_invalid_idx
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/mshr_hit
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/mshr_hit_vec
add wave -noupdate -group MEMORY_SYSTEM -group DTLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_dtlb_L1/mshr_full
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/clk_i
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/rst_ni
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/priv_mode_i
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/base_asid_i
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/flush_type_i
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/flush_asid_i
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/flush_page_i
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/vmem_on_i
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/abort_i
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/ic_areq_i
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/ic_areq_ready_o
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/ic_aresp_o
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/l2_req_o
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/l2_req_ready_i
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/l2_resp_i
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/l2_resp_ready_o
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/icache_itlb_effective_req_valid
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/effective_vaddr
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/valid_vec
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/exception_reg_en
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/exception_reg_clr
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/exception_q
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/vaddr_msb_difference_vec
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/vaddr_exception
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/vmem_exception
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/user_page_exception
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/effective_exception
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/flush
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/flush_vec
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/replace_entry
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/replacement_vec
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/waiting_l2c_ans
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/tlb_cond_rdy
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/hit
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/hit_vec
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/hit_idx
add wave -noupdate -group MEMORY_SYSTEM -group ITLB_L1 /tb_with_l2cemu/u_datapath/u_memory_system/i_itlb_L1/effective_vaddr_38
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 250
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {500 ps} {8980 ps}
