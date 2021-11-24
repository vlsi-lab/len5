// Copyright 2021 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: datapath.sv
// Author: Michele Caon
// Date: 19/11/2021

import len5_pkg::*;
import memory_pkg::*;
import csr_pkg::csr_priv_t;

module datapath #(
    parameter [XLEN-1:0]    BOOT_PC = 'h0
) (
    // Clock and reset
    input   logic               clk_i,
    input   logic               rst_n_i,

    // Datapath <--> L2$ emulator
    input   logic               l2c_l2arb_req_rdy_i,
    input   l2c_l2arb_ans_t     l2c_l2arb_ans_i,
    output  l2arb_l2c_req_t     l2arb_l2c_req_o,
    output  logic               l2arb_l2c_ans_rdy_o,
    output  logic               l2c_flush_o
);

    // ----------------
    // INTERNAL SIGNALS
    // ----------------

    // Main control unit <--> frontend
    // -------------------------------
    logic [ILEN-1:0]            fe_cu_instr;
    logic                       fe_cu_except_raised;

    // Main control unit <--> beckend
    // ------------------------------
    logic                       be_cu_stall;
    logic                       be_cu_flush;

    // Main control unit <--> memory system
    // ------------------------------------
    logic                       cu_mem_flush;
    logic                       cu_mem_abort;
    logic                       cu_mem_clr_l1tlb_mshr;
    logic                       cu_mem_clr_l2tlb_mshr;
    logic                       cu_mem_clear_dmshr_dregs;
    logic                       cu_mem_synch_l1dc_l2c;
    logic                       mem_cu_l2c_update_done;
    tlb_flush_e                 cu_mem_L1TLB_flush_type;
    tlb_flush_e                 cu_mem_L2TLB_flush_type;
    asid_t                      cu_mem_flush_asid;
    vpn_t                       cu_mem_flush_page;

    // CSRs <--> memory system
    // -----------------------
    logic                       csr_mem_vmem_on;
    logic                       csr_mem_sum_bit;
    logic                       csr_mem_mxr_bit;
    csr_priv_t                  csr_mem_priv_mode;
    csr_priv_t                  csr_mem_priv_mode_ls;
    asid_t                      csr_mem_base_asid;
    logic [PPN_LEN-1:0]         csr_mem_csr_root_ppn;

    // Main control unit <--> others
    // -----------------------------
    logic                       cu_others_stall;
    logic                       cu_others_flush;
    logic                       except_raised;

    // Frontend <--> I$
    // ----------------
    frontend_icache_req_t       fe_icache_req;
    logic                       icache_fe_addr_ready;
    icache_out_t                icache_fe_data;
    logic                       icache_fe_data_valid;
    logic                       fe_icache_data_ready;
    icache_frontend_ans_t       icache_fe_ans;

    // Frontend <--> backend
    // ---------------------
    logic                       be_fe_ready;
    logic                       fe_be_valid;
    logic [ILEN-1:0]            fe_be_instr;
    logic [XLEN-1:0]            fe_be_curr_pc;
    prediction_t                fe_be_pred;
    resolution_t                be_fe_res;
    logic                       fe_be_except;
    logic                       fe_be_except_code;
    logic                       be_fe_except;
    logic [XLEN-1:0]            be_fe_except_pc;

    // Backend <--> DTLB
    // -----------------
    dtlb_lsq_ans_t              dtlb_be_ans;
    dtlb_lsq_wup_t              dtlb_be_wup;
    logic                       dtlb_be_ready;
    lsq_dtlb_req_t              be_dtlb_req;

    // Backend <--> D$
    // ---------------
    l1dc_lsq_ans_t              dcache_be_ans;
    l1dc_lsq_wup_t              dcache_be_wup;
    logic                       dcache_be_ready;
    lsq_l1dc_req_t              be_dcache_req;

    // -----------------
    // MAIN CONTROL UNIT
    // -----------------

    // Reuse instruction and exception info from frontend to backend
    assign  fe_cu_instr         = fe_be_instr;
    assign  fe_cu_except_raised = fe_be_except;

    main_cu u_main_cu
    (
        .clk_i                  (clk_i),
        .rst_n_i                (rst_n_i),
        .fe_ins_i               (fe_cu_instr),
        .fe_except_raised_i     (fe_cu_except_raised),
        .be_stall_i             (be_cu_stall),
        .be_flush_i             (be_cu_flush),
        .stall_o                (cu_others_stall),
        .flush_o                (cu_others_flush),
        
        .mem_flush_o            (cu_mem_flush),
        .mem_abort_o            (cu_mem_abort),
        .mem_l2c_update_done    (mem_cu_l2c_update_done),
        .mem_clr_l1tlb_mshr     (cu_mem_clr_l1tlb_mshr),
        .mem_clr_l2tlb_mshr     (cu_mem_clr_l2tlb_mshr),
        .mem_clear_dmshr_dregs  (cu_mem_clear_dmshr_dregs),
        .mem_synch_l1dc_l2c     (cu_mem_synch_l1dc_l2c),
        .mem_L1TLB_flush_type   (cu_mem_L1TLB_flush_type),
        .mem_L2TLB_flush_type   (cu_mem_L2TLB_flush_type),
        .mem_flush_asid         (cu_mem_flush_asid),
        .mem_flush_page         (cu_mem_flush_page)
    );

    // ---------
    // FRONT-END
    // ---------

    frontend #(.HLEN(HLEN), .BTB_BITS(BTB_BITS), .BOOT_PC(BOOT_PC)) u_frontend
    (
        .clk_i                  (clk_i),
        .rst_n_i                (rst_n_i),
        .flush_i                (cu_others_flush),
        .addr_o                 (fe_icache_req.vaddr),
        .addr_valid_o           (fe_icache_req.valid),
        .addr_ready_i           (icache_fe_addr_ready),
        .data_i                 (icache_fe_data),
        .data_valid_i           (icache_fe_data_valid),
        .data_ready_o           (fe_icache_data_ready),
        .icache_frontend_ans_i  (icache_fe_ans),
        .issue_ready_i          (be_fe_ready),
        .issue_valid_o          (fe_be_valid),
        .instruction_o          (fe_be_instr),
        .curr_pc_o              (fe_be_curr_pc),
        .pred_o                 (fe_be_pred),
        .res_i                  (be_fe_res),
        .except_o               (fe_be_except),
        .except_code_o          (fe_be_except_code),
        .except_i               (be_fe_except),
        .except_pc_i            (be_fe_except_pc) 
    );

    // --------
    // BACK-END
    // --------

    // TODO: what is fe_be_pred.pc?

    backend u_backend
    (
        .clk_i                      (clk_i),
        .rst_n_i                    (rst_n_i),
        .flush_i                    (cu_others_flush),
        .main_cu_stall_o            (be_cu_stall),
        .main_cu_flush_o            (be_cu_flush),
        .fetch_valid_i              (fe_be_valid),
        .fetch_ready_o              (be_fe_ready),
        .fetch_curr_pc_i            (fe_be_curr_pc),
        .fetch_instr_i              (fe_be_instr),
        .fetch_pred_target_i        (fe_be_pred.target),
        .fetch_pred_taken_i         (fe_be_pred.taken),
        .fetch_except_raised_i      (fe_be_except),
        .fetch_except_code_i        (fe_be_except_code),
        .fetch_res_pc_o             (be_fe_res.pc),
        .fetch_res_target_o         (be_fe_res.target),
        .fetch_res_taken_o          (be_fe_res.taken),
        .fetch_res_valid_o          (be_fe_res.valid),
        .fetch_res_mispredict_o     (be_fe_res.mispredict),
        .fetch_except_raised_o      (be_fe_except),
        .fetch_except_pc_o          (be_fe_except_pc),
        .dtlb_ans_i                 (dtlb_be_ans),
        .dtlb_wup_i                 (dtlb_be_wup),
        .dtlb_ready_i               (dtlb_be_ready),
        .dtlb_req_o                 (be_dtlb_req),
        .dcache_ans_i               (dcache_be_ans),
        .dcache_wup_i               (dcache_be_wup),
        .dcache_ready_i             (dcache_be_ready),
        .dcache_req_o               (be_dcache_req),
        .mem_vmem_on_o              (csr_mem_vmem_on),
        .mem_sum_bit_o              (csr_mem_sum_bit),
        .mem_mxr_bit_o              (csr_mem_mxr_bit),
        .mem_priv_mode_o            (csr_mem_priv_mode),
        .mem_priv_mode_ls_o         (csr_mem_priv_mode_ls),
        .mem_base_asid_o            (csr_mem_base_asid),
        .mem_csr_root_ppn_o         (csr_mem_csr_root_ppn)
    );

    // -------------
    // MEMORY-SYSTEM
    // -------------

    memory_system_with_ssram u_memory_system
    (
        .clk_i                      (clk_i),
        .rst_ni                     (rst_n_i),

        .flush_i                    (cu_mem_flush),
        .abort_i                    (cu_mem_abort),
        .clr_l1tlb_mshr_i           (cu_mem_clr_l1tlb_mshr),
        .clr_l2tlb_mshr_i           (cu_mem_clr_l2tlb_mshr),
        .clear_dmshr_dregs_i        (cu_mem_clear_dmshr_dregs),

        .synch_l1dc_l2c_i           (cu_mem_synch_l1dc_l2c),
        .l2c_update_done_o          (mem_cu_l2c_update_done),

        .vmem_on_i                  (csr_mem_vmem_on),
        .sum_bit_i                  (csr_mem_sum_bit),
        .mxr_bit_i                  (csr_mem_mxr_bit),
        .priv_mode_i                (csr_mem_priv_mode),
        .priv_mode_ls_i             (csr_mem_priv_mode_ls),
        .base_asid_i                (csr_mem_base_asid),
        .csr_root_ppn_i             (csr_mem_csr_root_ppn),

        .L1TLB_flush_type_i         (cu_mem_L1TLB_flush_type),
        .L2TLB_flush_type_i         (cu_mem_L2TLB_flush_type),
        .flush_asid_i               (cu_mem_flush_asid),
        .flush_page_i               (cu_mem_flush_page),

        .frontend_icache_req_i      (fe_icache_req),
        .icache_frontend_rdy_o      (icache_fe_addr_ready),
        .icache_frontend_ans_o      (icache_fe_ans),

        .lsq_dtlb_req_i             (be_dtlb_req),
        .dtlb_lsq_req_rdy_o         (dtlb_be_ready),
        .dtlb_lsq_ans_o             (dtlb_be_ans),
        .dtlb_lsq_wup_o             (dtlb_be_wup),

        .lsq_l1dc_req_i             (be_dcache_req),
        .l1dc_lsq_req_rdy_o         (dcache_be_ready),
        .l1dc_lsq_ans_o             (dcache_be_ans),
        .l1dc_lsq_wup_o             (dcache_be_wup),

        .l2arb_l2c_req_o            (l2arb_l2c_req_o),
        .l2c_l2arb_req_rdy_i        (l2c_l2arb_req_rdy_i),
        .l2c_l2arb_ans_i            (l2c_l2arb_ans_i),
        .l2arb_l2c_ans_rdy_o        (l2arb_l2c_ans_rdy_o)
    );

    // -----------------
    // OUTPUT EVALUATION
    // -----------------

    // L2$ flush
    assign  l2c_flush_o         = cu_mem_flush;
    
endmodule