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
import fetch_pkg::*;
import csr_pkg::csr_priv_t;

module datapath #(
    parameter [XLEN-1:0]    BOOT_PC = 'h0
) (
    // Clock and reset
    input   logic               clk_i,
    input   logic               rst_n_i,

    // Datapath <--> memory emulator
    input   logic               mem_valid_i,
    input   logic               mem_ready_i,
    output  logic               mem_valid_o,
    output  logic               mem_ready_o,
    input   mem_ans_t           mem_ans_i,
    output  mem_req_t           mem_req_o          
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
    logic                       be_cu_resume;
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

    // Main control unit <--> others
    // -----------------------------
    logic                       cu_others_stall;
    logic                       cu_others_flush;
    logic                       except_raised;

    // Frontend <--> backend
    // ---------------------
    logic                       be_fe_ready;
    logic                       fe_be_valid;
    logic [ILEN-1:0]            fe_be_instr;
    logic [XLEN-1:0]            fe_be_curr_pc;
    prediction_t                fe_be_pred;
    logic                       be_fe_res_valid;
    resolution_t                be_fe_res;
    logic                       fe_be_except;
    except_code_t               fe_be_except_code;
    logic                       be_fe_except;
    logic [XLEN-1:0]            be_fe_except_pc;

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
        .be_resume_i            (be_cu_resume),
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

    

    // --------
    // BACK-END
    // --------

    backend u_backend
    (
        .clk_i                      (clk_i),
        .rst_n_i                    (rst_n_i),
        .flush_i                    (cu_others_flush),
        .main_cu_stall_o            (be_cu_stall),
        .main_cu_resume_o           (be_cu_resume),
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
        .fetch_res_valid_o          (be_fe_res_valid),
        .fetch_res_mispredict_o     (be_fe_res.mispredict),
        .fetch_except_raised_o      (be_fe_except),
        .fetch_except_pc_o          (be_fe_except_pc),
        .mem_valid_i                (mem_valid_i),
        .mem_ready_i                (mem_ready_i),
        .mem_valid_o                (mem_valid_o),
        .mem_ready_o                (mem_ready_o),
        .mem_req_o                  (mem_req_o),
        .mem_ans_i                  (mem_ans_i)
    );

    // -------------
    // MEMORY-SYSTEM
    // -------------
    // NOTE: in the bare-metal version, the load-store unit is directly
    //       connected to the memory.
    
endmodule