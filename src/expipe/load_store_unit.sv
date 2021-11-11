// Copyright 2019 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: load_store_unit.sv
// Author: Michele Caon
// Date: 27/10/2019

// Include LEN5 configuration
`include "len5_config.svh"

import expipe_pkg::*;

import memory_pkg::*;
import len5_pkg::*;
import csr_pkg::satp_mode_t;
import csr_pkg::BARE; 
import csr_pkg::SV39;
import csr_pkg::SV48;

module load_store_unit (
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,
	//input   logic				stall,

    input   satp_mode_t             vm_mode_i,

    // Handshake from/to issue arbiter
    input   logic                   issue_lb_valid_i,
    input   logic                   issue_sb_valid_i,
    output  logic                   lb_issue_ready_o,
    output  logic                   sb_issue_ready_o,

    // Data from the decode stage
    input   ldst_type_t             ldst_type_i,
    input   logic                   rs1_ready_i,    
    input   logic [ROB_IDX_LEN-1:0] rs1_idx_i,
    input   logic [XLEN-1:0]        rs1_value_i,
    input   logic                   rs2_ready_i,    
    input   logic [ROB_IDX_LEN-1:0] rs2_idx_i,
    input   logic [XLEN-1:0]        rs2_value_i,
    input   logic [I_IMM-1:0]       imm_value_i,    
    input   logic [ROB_IDX_LEN-1:0] dest_idx_i,

    // Handshake and data from/to the TLB
    input dtlb_lsq_ans_t          dtlb_ans_i,
    input dtlb_lsq_wup_t          dtlb_wup_i,
    input   logic                       dtlb_ready_i,
    output  lsq_dtlb_req_t              dtlb_req_o,

    // Handshake and data from/to the D$
    input l1dc_lsq_ans_t          dcache_ans_i,
    input l1dc_lsq_wup_t          dcache_wup_i,
    input   logic                       dcache_ready_i,
    output  lsq_l1dc_req_t              dcache_req_o,

    // Control from/to the ROB
    input   logic [ROB_IDX_LEN-1:0] rob_head_idx_i,
    output  logic                   rob_store_committing_o,

    // Hanshake from/to the CDB 
    input   logic                   cdb_lb_valid_i,
    input   logic                   cdb_sb_valid_i,
    input   logic                   cdb_lb_ready_i,
    input   logic                   cdb_sb_ready_i,
    output  logic                   lb_cdb_valid_o,
    output  logic                   sb_cdb_valid_o,

    // Data from/to the CDB
    input cdb_data_t              cdb_lsb_data_i,
    output  cdb_data_t              lb_cdb_data_o,
    output  cdb_data_t              sb_cdb_data_o
);

    // DEFINITIONS

    // -----------------------------
    // LOAD BUFFER <--> STORE BUFFER
    // -----------------------------

    logic [XLEN-1:0]            vfwd_vaddr;
    logic [XLEN-1:0]            pfwd_paddr;
    ldst_type_t                 vfwd_ldtype;
    ldst_type_t                 pfwd_ldtype;    
    logic [STBUFF_IDX_LEN:0]    vfwd_older_stores;
    logic [STBUFF_IDX_LEN:0]    pfwd_older_stores;
    logic [STBUFF_IDX_LEN:0]    inflight_store_cnt; 
    logic                       lb_store_committing; 
    logic                       vfwd_hit;
    logic                       vfwd_depfree;
    logic                       pfwd_hit;
    logic                       pfwd_depfree;
    logic [XLEN-1:0]            vfwd_value;
    logic [XLEN-1:0]            pfwd_value;

    // --------------------------------------------
    // LOAD/STORE BUFFER <--> VIRTUAL ADDRESS ADDER
    // --------------------------------------------
    
    // (LOAD/STORE BUFFER --> VIRTUAL ADDRESS ADDER) HS ARBITER
    logic                       lb_vadderarb_valid;
    logic                       sb_vadderarb_valid;
    logic                       vadderarb_vadder_valid;
    logic                       vadder_vadderarb_ready;
    logic                       vadderarb_lb_ready;
    logic                       vadderarb_sb_ready;

    // (LOAD/STORE BUFFER --> VIRTUAL ADDRESS ADDER) MUX
    // Load buffer --> MUX
    logic                       lb_vaddermux_isstore;
    logic [XLEN-1:0]            lb_vaddermux_rs1_value;
    logic [I_IMM-1:0]           lb_vaddermux_imm_value;
    logic [LDBUFF_IDX_LEN-1:0]  lb_vaddermux_idx;
    ldst_type_t                 lb_vaddermux_ldtype;
    // Store buffer --> MUX
    logic                       sb_vaddermux_isstore;
    logic [XLEN-1:0]            sb_vaddermux_rs1_value;
    logic [I_IMM-1:0]           sb_vaddermux_imm_value;
    logic [STBUFF_IDX_LEN-1:0]  sb_vaddermux_idx;
    ldst_type_t                 sb_vaddermux_sttype;
    // MUX --> Virtual address adder
    logic                       vaddermux_vadder_is_store;
    logic [XLEN-1:0]            vaddermux_vadder_rs1_value;
    logic [I_IMM-1:0]           vaddermux_vadder_imm_value;
    logic [BUFF_IDX_LEN-1:0]    vaddermux_vadder_lsb_idx;
    ldst_type_t                 vaddermux_vadder_ldst_type;

    // (VIRTUAL ADDRESS ADDER --> LOAD/STORE BUFFER) HS DECODER
    logic                       vadder_vadderdec_is_store;
    logic                       vadder_vadderdec_valid;
    logic                       vadderdec_lb_valid;
    logic                       vadderdec_sb_valid;
    logic                       lb_vadderdec_ready;
    logic                       sb_vadderdec_ready;
    logic                       vadderdec_vadder_ready;

    // VADDER MUX SEL
    logic                       vaddermux_sel;
    
    // (VIRTUAL ADDRESS ADDER --> LOAD/STORE BUFFER) DATA
    // Connected to both the load buffer and the store buffer inputs
    logic [XLEN-1:0]            vadder_lsb_vaddr;
    logic [BUFF_IDX_LEN-1:0]    vadder_lsb_idx;
    vadder_except_t             vadder_lsb_except;

    // ---------------------------
    // LOAD/STORE BUFFER <--> DTLB
    // ---------------------------

    // (LOAD/STORE BUFFER --> DTLB) HS ARBITER
    logic                       lb_dtlbarb_valid;
    logic                       sb_dtlbarb_valid;
    logic                       dtlbarb_dtlb_valid;
    logic                       dtlb_dtlbarb_ready;
    logic                       dtlbarb_lb_ready;
    logic                       dtlbarb_sb_ready;

    // (LOAD/STORE BUFFER --> DTLB) MUX
    // Load buffer --> MUX
    logic                       lb_dtlbmux_isstore;
    logic [VPN_LEN-1:0]         lb_dtlbmux_vaddr;
    logic [LDBUFF_IDX_LEN-1:0]  lb_dtlbmux_idx;
    // Store buffer --> MUX
    logic                       sb_dtlbmux_isstore;
    logic [VPN_LEN-1:0]         sb_dtlbmux_vaddr;
    logic [STBUFF_IDX_LEN-1:0]  sb_dtlbmux_idx;
    // MUX --> DTLB
    logic                       dtlbmux_dtlb_isstore;
    logic [VPN_LEN-1:0]         dtlbmux_dtlb_vaddr;
    logic [BUFF_IDX_LEN-1:0]    dtlbmux_dtlb_idx;

    // (DTLB --> LOAD/STORE BUFFER) HS DECODER
    logic                       dtlb_dtlbdec_is_store;
    logic                       dtlb_dtlbdec_ans_valid;
    logic                       dtlb_dtlbdec_wup_valid;
    logic                       dtlbdec_lb_ans_valid;
    logic                       dtlbdec_sb_ans_valid;
    logic                       dtlbdec_lsb_wup_valid;
    logic                       lb_dtlbdec_ready;
    logic                       sb_dtlbdec_ready;
    logic                       dtlbdec_dtlb_ready;

    // (DTLB --> LOAD/STORE BUFFER) DATA
    // Connected to both the load buffer and the store buffer inputs
    logic [VPN_LEN-1:0]         dtlb_lsb_vaddr;
    logic [PPN_LEN-1:0]         dtlb_lsb_ppn;
    exception_e                 dtlb_lsb_except;
    logic [BUFF_IDX_LEN-1:0]  dtlb_lsb_idx;

    // DTLB MUX SEL
    logic                       dtlbmux_sel;

    // ---------------------------------
    // LOAD/STORE BUFFER <--> DATA CACHE
    // ---------------------------------
    // (LOAD/STORE BUFFER --> D$) HS ARBITER
    logic                       lb_dcachearb_valid;
    logic                       sb_dcachearb_valid;
    logic                       dcachearb_dcache_valid;
    logic                       dcache_dcachearb_ready;
    logic                       dcachearb_lb_ready;
    logic                       dcachearb_sb_ready;

    // (LOAD/STORE BUFFER --> D$) MUX
    // Load buffer --> MUX
    logic                       lb_dcachemux_isstore;
    logic [XLEN-1:0]            lb_dcachemux_paddr;
    logic [LDBUFF_IDX_LEN-1:0]  lb_dcachemux_idx;
    // Store buffer --> MUX
    logic                       sb_dcachemux_isstore;
    logic [XLEN-1:0]            sb_dcachemux_paddr;
    logic [XLEN-1:0]            sb_dcachemux_value;
    logic [STBUFF_IDX_LEN-1:0]  sb_dcachemux_idx;
    ldst_type_t                 sb_dcachemux_sttype;
    // MUX --> D$
    logic                       dcachemux_dcache_isstore;
    logic [XLEN-1:0]            dcachemux_dcache_paddr;
    logic [XLEN-1:0]            dcachemux_dcache_value;
    logic [BUFF_IDX_LEN-1:0]    dcachemux_dcache_idx;
    ldst_type_t                 dcachemux_dcache_sttype;

    // (D$ --> LOAD/STORE BUFFER) HS DECODER
    logic                       dcache_dcachedec_is_store;
    logic                       dcache_dcachedec_ans_valid;
    logic                       dcache_dcachedec_wup_valid;
    logic                       dcachedec_lb_ans_valid;
    logic                       dcachedec_lb_wup_valid;
    logic                       dcachedec_sb_ans_valid;
    logic                       dcachedec_sb_wup_valid;
    logic                       lb_dcachedec_ready;
    logic                       sb_dcachedec_ready;
    logic                       dcachedec_dcache_ready;

    // (D$ --> LOAD/STORE BUFFER) DATA
    // Connected to both the load buffer and the store buffer inputs
    logic [DCACHE_L1_LINE_A_LEN-1:0] dcache_lsb_paddr;
    logic [XLEN-1:0]            dcache_lsb_value;
    logic [BUFF_IDX_LEN-1:0]  dcache_lsb_idx;

    // D$ MUX SEL
    logic                       dcachemux_sel;


    // MODULES INSTANTIATION

    // -----------
    // LOAD BUFFER
    // -----------
    load_buffer u_load_buffer (
        .clk_i                  (clk_i),
        .rst_n_i                (rst_n_i),
        .flush_i                (flush_i),
		//.stall(stall),

        .vm_mode_i              (vm_mode_i),

        // Handshake from/to issue arbiter
        .issue_logic_valid_i    (issue_lb_valid_i),
        .issue_logic_ready_o    (lb_issue_ready_o),

        // Data from the decode stage
        .load_type_i            (ldst_type_i),
        .rs1_ready_i            (rs1_ready_i),    
        .rs1_idx_i              (rs1_idx_i),
        .rs1_value_i            (rs1_value_i),
        .imm_value_i            (imm_value_i),    
        .dest_idx_i             (dest_idx_i),

        // Handshake from/to the virtual address adder arbiter
        .vadder_valid_i         (vadderdec_lb_valid),
        .vadder_ready_i         (vadderarb_lb_ready),
        .vadder_valid_o         (lb_vadderarb_valid),
        .vadder_ready_o         (lb_vadderdec_ready),

        // Data from/to the virtual address adder
        .vadder_vaddr_i         (vadder_lsb_vaddr),
        .vadder_idx_i           (vadder_lsb_idx[LDBUFF_IDX_LEN-1:0]),
        .vadder_except_i        (vadder_lsb_except),
        .vadder_isstore_o       (lb_vaddermux_isstore),
        .rs1_value_o            (lb_vaddermux_rs1_value),
        .imm_value_o            (lb_vaddermux_imm_value),
        .vadder_idx_o           (lb_vaddermux_idx),
        .vadder_ldtype_o        (lb_vaddermux_ldtype),

        // Handshake from/to the TLB
        .dtlb_wu_valid_i        (dtlbdec_lsb_wup_valid),
        .dtlb_ans_valid_i       (dtlbdec_lb_ans_valid),
        .dtlb_ready_i           (dtlbarb_lb_ready),
        .dtlb_valid_o           (lb_dtlbarb_valid), 
        .dtlb_ready_o           (lb_dtlbdec_ready),

        // Data from/to the TLB
        .dtlb_vaddr_i           (dtlb_lsb_vaddr),
        .dtlb_ppn_i             (dtlb_lsb_ppn),
        .dtlb_except_i          (dtlb_lsb_except),
        .dtlb_idx_i             (dtlb_lsb_idx[LDBUFF_IDX_LEN-1:0]),
        .dtlb_isstore_o         (lb_dtlbmux_isstore),
        .dtlb_vaddr_o           (lb_dtlbmux_vaddr),
        .dtlb_idx_o             (lb_dtlbmux_idx),

        // Handshake from/to the D$
        .dcache_wu_valid_i      (dcachedec_lb_wup_valid),
        .dcache_ans_valid_i     (dcachedec_lb_ans_valid),
        .dcache_ready_i         (dcachearb_lb_ready),
        .dcache_valid_o         (lb_dcachearb_valid),
        .dcache_ready_o         (lb_dcachedec_ready), //

        // Data from/to the D$
        .dcache_lineaddr_i         (dcache_lsb_paddr),
        .dcache_value_i         (dcache_lsb_value),
        .dcache_idx_i           (dcache_lsb_idx[LDBUFF_IDX_LEN-1:0]),
        .dcache_isstore_o       (lb_dcachemux_isstore),
        .dcache_paddr_o         (lb_dcachemux_paddr),
        .dcache_idx_o           (lb_dcachemux_idx),

        // Data from/to the store buffer
        .inflight_store_cnt_i   (inflight_store_cnt), 
        .store_committing_i     (lb_store_committing), 
        .vfwd_hit_i             (vfwd_hit),
        .vfwd_depfree_i         (vfwd_depfree),
        .pfwd_hit_i             (pfwd_hit),
        .pfwd_depfree_i         (pfwd_depfree),
        .vfwd_value_i           (vfwd_value),
        .pfwd_value_i           (pfwd_value),
        .vfwd_vaddr_o           (vfwd_vaddr),
        .pfwd_paddr_o           (pfwd_paddr),
        .vfwd_ldtype_o          (vfwd_ldtype),
        .pfwd_ldtype_o          (pfwd_ldtype),
        .vfwd_older_stores_o    (vfwd_older_stores),
        .pfwd_older_stores_o    (pfwd_older_stores),

        // Hanshake from/to the CDB 
        .cdb_ready_i            (cdb_lb_ready_i),
        .cdb_valid_i            (cdb_lb_valid_i),  
        .cdb_valid_o            (lb_cdb_valid_o),

        // Data from/to the CDB
        .cdb_idx_i              (cdb_lsb_data_i.rob_idx),
        .cdb_data_i             (cdb_lsb_data_i.value),
        .cdb_except_raised_i    (cdb_lsb_data_i.except_raised),
        .cdb_idx_o              (lb_cdb_data_o.rob_idx),
        .cdb_data_o             (lb_cdb_data_o.value),
        .cdb_except_raised_o    (lb_cdb_data_o.except_raised),
        .cdb_except_o           (lb_cdb_data_o.except_code)
    );

    // ------------
    // STORE BUFFER
    // ------------

    store_buffer u_store_buffer (
        .clk_i                  (clk_i),
        .rst_n_i                (rst_n_i),
        .flush_i                (flush_i),
		//.stall(stall),

        .vm_mode_i              (vm_mode_i),          

        // Handshake from/to issue arbiter
        .issue_logic_valid_i    (issue_sb_valid_i),
        .issue_logic_ready_o    (sb_issue_ready_o),

        // Data from the decode stage
        .store_type_i           (ldst_type_i),
        .rs1_ready_i            (rs1_ready_i),        
        .rs1_idx_i              (rs1_idx_i),
        .rs1_value_i            (rs1_value_i),
        .rs2_ready_i            (rs2_ready_i),  
        .rs2_idx_i              (rs2_idx_i),
        .rs2_value_i            (rs2_value_i),
        .imm_value_i            (imm_value_i), 
        .dest_idx_i             (dest_idx_i),

        // Handshake from/to the virtual address adder
        .vadder_valid_i         (vadderdec_sb_valid),
        .vadder_ready_i         (vadderarb_sb_ready),
        .vadder_valid_o         (sb_vadderarb_valid),
        .vadder_ready_o         (sb_vadderdec_ready),

        // Data from/to the virtual address adder
        .vadder_vaddr_i         (vadder_lsb_vaddr),
        .vadder_idx_i           (vadder_lsb_idx[STBUFF_IDX_LEN-1:0]),
        .vadder_except_i        (vadder_lsb_except),
        .vadder_isstore_o       (sb_vaddermux_isstore),
        .rs1_value_o            (sb_vaddermux_rs1_value),
        .imm_value_o            (sb_vaddermux_imm_value),
        .vadder_idx_o           (sb_vaddermux_idx),
        .vadder_sttype_o        (sb_vaddermux_sttype),

        // Handshake from/to the TLB
        .dtlb_wu_valid_i        (dtlbdec_lsb_wup_valid),
        .dtlb_ans_valid_i       (dtlbdec_sb_ans_valid),
        .dtlb_ready_i           (dtlbarb_sb_ready),
        .dtlb_valid_o           (sb_dtlbarb_valid), 
        .dtlb_ready_o           (sb_dtlbdec_ready), //

        // Data from/to the TLB
        .dtlb_vaddr_i           (dtlb_lsb_vaddr),
        .dtlb_ppn_i             (dtlb_lsb_ppn),
        .dtlb_except_i          (dtlb_lsb_except),
        .dtlb_idx_i             (dtlb_lsb_idx[STBUFF_IDX_LEN-1:0]),
        .dtlb_isstore_o         (sb_dtlbmux_isstore),
        .dtlb_vaddr_o           (sb_dtlbmux_vaddr),
        .dtlb_idx_o             (sb_dtlbmux_idx),

        // Handshake from/to the D$
        .dcache_wu_valid_i      (dcachedec_sb_wup_valid),
        .dcache_ans_valid_i     (dcachedec_sb_ans_valid),
        .dcache_ready_i         (dcachearb_sb_ready),
        .dcache_valid_o         (sb_dcachearb_valid),
        .dcache_ready_o         (sb_dcachedec_ready), //

        // Data from/to the D$
        .dcache_lineaddr_i         (dcache_lsb_paddr),
        .dcache_idx_i           (dcache_lsb_idx[STBUFF_IDX_LEN-1:0]),
        .dcache_isstore_o       (sb_dcachemux_isstore),
        .dcache_paddr_o         (sb_dcachemux_paddr),
        .dcache_value_o         (sb_dcachemux_value),
        .dcache_idx_o           (sb_dcachemux_idx),
        .dcache_sttype_o        (sb_dcachemux_sttype),

        // Data from/to the load buffer
        .vfwd_vaddr_i           (vfwd_vaddr),
        .pfwd_paddr_i           (pfwd_paddr),
        .vfwd_ldtype_i          (vfwd_ldtype),
        .pfwd_ldtype_i          (pfwd_ldtype),        
        .vfwd_older_stores_i    (vfwd_older_stores),
        .pfwd_older_stores_i    (pfwd_older_stores),
        .inflight_store_cnt_o   (inflight_store_cnt), 
        .lb_store_committing_o  (lb_store_committing), 
        .vfwd_hit_o             (vfwd_hit),
        .vfwd_depfree_o         (vfwd_depfree),
        .pfwd_hit_o             (pfwd_hit),
        .pfwd_depfree_o         (pfwd_depfree),
        .vfwd_value_o           (vfwd_value),
        .pfwd_value_o           (pfwd_value),

        // Data from/to the ROB
        .rob_head_idx_i         (rob_head_idx_i),
        .rob_store_committing_o (rob_store_committing_o),

        // Hanshake from/to the CDB 
        .cdb_ready_i            (cdb_sb_ready_i),
        .cdb_valid_i            (cdb_sb_valid_i), 
        .cdb_valid_o            (sb_cdb_valid_o),

        // Data from/to the CDB
        .cdb_idx_i              (cdb_lsb_data_i.rob_idx),
        .cdb_data_i             (cdb_lsb_data_i.value),
        .cdb_except_raised_i    (cdb_lsb_data_i.except_raised),
        .cdb_idx_o              (sb_cdb_data_o.rob_idx),
        .cdb_data_o             (sb_cdb_data_o.value),
        .cdb_except_raised_o    (sb_cdb_data_o.except_raised),
        .cdb_except_o           (sb_cdb_data_o.except_code)
    );


    // ---------------------
    // VIRTUAL ADDRESS ADDER
    // ---------------------
    vaddr_adder #( .IDX_LEN (BUFF_IDX_LEN) ) u_vaddr_adder
    (
        .clk_i          (clk_i),
        .rst_n_i        (rst_n_i),
        .flush_i        (flush_i),

        // Virtual memory configuration
        .vm_mode_i      (vm_mode_i), 

        // Handshake from/to the load/store buffers
        .lsb_valid_i    (vadderarb_vadder_valid),
        .lsb_ready_i    (vadderdec_vadder_ready),
        .lsb_valid_o    (vadder_vadderdec_valid),
        .lsb_ready_o    (vadder_vadderarb_ready),

        // Data from/to the load/store buffers
        .is_store_i     (vaddermux_vadder_is_store),
        .rs1_value_i    (vaddermux_vadder_rs1_value),
        .imm_value_i    (vaddermux_vadder_imm_value),
        .lsb_idx_i      (vaddermux_vadder_lsb_idx),
        .ldst_type_i    (vaddermux_vadder_ldst_type),
        .is_store_o     (vadder_vadderdec_is_store),
        .vaddr_o        (vadder_lsb_vaddr),
        .lsb_idx_o      (vadder_lsb_idx),
        .except_o       (vadder_lsb_except)
    );

    // --------------------------------
    // VIRTUAL ADDRESS ADDER HS ARBITER
    // --------------------------------
    `ifdef ENABLE_STORE_PRIO_2WAY_ARBITER
    // The store buffer, connected to valid_i[0] is given higher priority than the load buffer. This should increase the hit ratio of the store to load forwarding. However, it increases the load execution latency. Depending on the scenario, performance may be better or worse than the fair arbiter
    prio_2way_arbiter vadder_arbiter (
        .valid_i        ({ lb_vadderarb_valid, sb_vadderarb_valid }),
        .ready_i        (vadder_vadderarb_ready),
        .valid_o        (vadderarb_vadder_valid),
        .ready_o        ({ vadderarb_lb_ready, vadderarb_sb_ready }),
        .select_o       (vaddermux_sel) // 1 if load buffer is served
    );
    `else
    fair_2way_arbiter vadder_arbiter (
        .clk_i          (clk_i),
        .rst_n_i        (rst_n_i),
        .valid_i        ({ lb_vadderarb_valid, sb_vadderarb_valid }),
        .ready_i        (vadder_vadderarb_ready),
        .valid_o        (vadderarb_vadder_valid),
        .ready_o        ({ vadderarb_lb_ready, vadderarb_sb_ready }),
        .select_o       (vaddermux_sel) // 1 if load buffer is served
    );
    `endif

    // -------------------------
    // VIRTUAL ADDRESS ADDER MUX
    // -------------------------
    always_comb begin: vadder_mux
        if (vaddermux_sel) begin
            vaddermux_vadder_is_store   = lb_vaddermux_isstore;
            vaddermux_vadder_rs1_value  = lb_vaddermux_rs1_value;
            vaddermux_vadder_imm_value  = lb_vaddermux_imm_value;
            vaddermux_vadder_lsb_idx    = { {(BUFF_IDX_LEN-LDBUFF_IDX_LEN){1'b0}}, lb_vaddermux_idx }; // padd with zeroes if the load buffer is smaller than the store buffer
            vaddermux_vadder_ldst_type  = lb_vaddermux_ldtype;
        end else begin
            vaddermux_vadder_is_store   = sb_vaddermux_isstore;
            vaddermux_vadder_rs1_value  = sb_vaddermux_rs1_value;
            vaddermux_vadder_imm_value  = sb_vaddermux_imm_value;
            vaddermux_vadder_lsb_idx    = { {(BUFF_IDX_LEN-STBUFF_IDX_LEN){1'b0}}, sb_vaddermux_idx }; // padd with zeroes if the store buffer is smaller than the load buffer
            vaddermux_vadder_ldst_type  = sb_vaddermux_sttype;
        end
    end

    // --------------------------------
    // VIRTUAL ADDRESS ADDER HS DECODER
    // --------------------------------
    always_comb begin: vadder_hs_decoder
        if (vadder_vadderdec_is_store) begin
            vadderdec_lb_valid      = 1'b0;
            vadderdec_sb_valid      = vadder_vadderdec_valid;
            vadderdec_vadder_ready  = sb_vadderdec_ready;
        end else begin
            vadderdec_lb_valid      = vadder_vadderdec_valid;
            vadderdec_sb_valid      = 1'b0;
            vadderdec_vadder_ready  = lb_vadderdec_ready;
        end
    end

    // --------------------
    // DTLB TYPE CONVERSION
    // --------------------
    // lsq_dtlb_req_t
    assign dtlb_req_o.vpn       = dtlbmux_dtlb_vaddr;
    assign dtlb_req_o.is_store  = dtlbmux_dtlb_isstore;
    assign dtlb_req_o.lsq_addr  = dtlbmux_dtlb_idx;
    assign dtlb_req_o.valid     = dtlbarb_dtlb_valid;

    // dtlb_lsq_ans_t/dtlb_lsq_wup_t
    assign dtlb_dtlbdec_ans_valid   = dtlb_ans_i.valid; 
    assign dtlb_dtlbdec_wup_valid   = dtlb_wup_i.valid;
    always_comb begin
        if (dtlb_wup_i.valid) begin
            dtlb_lsb_ppn            = dtlb_ans_i.ppn;       // data provided in the ans signal
            dtlb_lsb_except         = dtlb_ans_i.exception; // data provided in the ans signal
            dtlb_lsb_idx            = 0;
            dtlb_lsb_vaddr          = dtlb_wup_i.vpn;
        end else begin
            dtlb_lsb_ppn            = dtlb_ans_i.ppn;
            dtlb_lsb_except         = dtlb_ans_i.exception;
            dtlb_lsb_idx            = dtlb_ans_i.lsq_addr;
            dtlb_lsb_vaddr          = 0;
        end
        dtlb_dtlbdec_is_store   = dtlb_ans_i.was_store;
    end

    // ---------------
    // DTLB HS ARBITER
    // ---------------

    assign dtlb_dtlbarb_ready = dtlb_ready_i;
    
    `ifdef ENABLE_STORE_PRIO_2WAY_ARBITER
    // The store buffer, connected to valid_i[0] is given higher priority than the load buffer. This should increase the hit ratio of the store to load forwarding. However, it increases the load execution latency. Depending on the scenario, performance may be better or worse than the fair arbiter
    prio_2way_arbiter dtlb_hs_arbiter (
        .valid_i        ({ lb_dtlbarb_valid, sb_dtlbarb_valid }),
        .ready_i        (dtlb_dtlbarb_ready),
        .valid_o        (dtlbarb_dtlb_valid),
        .ready_o        ({ dtlbarb_lb_ready, dtlbarb_sb_ready }),
        .select_o       (dtlbmux_sel) // 1 if load buffer is served
    );
    `else
    fair_2way_arbiter dtlb_hs_arbiter (
        .clk_i          (clk_i),
        .rst_n_i        (rst_n_i),
        .valid_i        ({ lb_dtlbarb_valid, sb_dtlbarb_valid }),
        .ready_i        (dtlb_dtlbarb_ready),
        .valid_o        (dtlbarb_dtlb_valid),
        .ready_o        ({ dtlbarb_lb_ready, dtlbarb_sb_ready }),
        .select_o       (dtlbmux_sel) // 1 if load buffer is served
    );
    `endif

    // --------
    // DTLB MUX
    // --------
    always_comb begin: dtlb_mux
        if (dtlbmux_sel) begin
            dtlbmux_dtlb_isstore    = lb_dtlbmux_isstore;
            dtlbmux_dtlb_vaddr      = lb_dtlbmux_vaddr;
            dtlbmux_dtlb_idx        = { {(BUFF_IDX_LEN-LDBUFF_IDX_LEN){1'b0}}, lb_dtlbmux_idx }; // padd with zeroes if the load buffer is smaller than the store buffer
        end else begin
            dtlbmux_dtlb_isstore    = sb_dtlbmux_isstore;
            dtlbmux_dtlb_vaddr      = sb_dtlbmux_vaddr;
            dtlbmux_dtlb_idx        = { {(BUFF_IDX_LEN-STBUFF_IDX_LEN){1'b0}}, sb_dtlbmux_idx }; // padd with zeroes if the load buffer is smaller than the store buffer
        end
    end

    // ---------------
    // DTLB HS DECODER
    // ---------------
    always_comb begin: dtlb_hs_decoder
        if (dtlb_dtlbdec_is_store) begin
            dtlbdec_lb_ans_valid    = 1'b0;  
            dtlbdec_sb_ans_valid    = dtlb_dtlbdec_ans_valid;
            dtlbdec_dtlb_ready      = sb_dtlbdec_ready;
        end else begin
            dtlbdec_lb_ans_valid    = dtlb_dtlbdec_ans_valid;
            dtlbdec_sb_ans_valid    = 1'b0;
            dtlbdec_dtlb_ready      = lb_dtlbdec_ready;
        end
        dtlbdec_lsb_wup_valid       = dtlb_dtlbdec_wup_valid;
    end


    // --------------------
    // DCACHE TYPE CONVERSION
    // --------------------
    // lsq_l1dc_req_t
    assign dcache_req_o.paddr       = dcachemux_dcache_paddr;
    assign dcache_req_o.data        = dcachemux_dcache_value;
    assign dcache_req_o.req_type    = (dcachemux_dcache_isstore) ? Store : Load;
    always_comb begin
        case(dcachemux_dcache_sttype)
                LS_BYTE, LS_BYTE_U:         dcache_req_o.store_width = B;
                LS_HALFWORD, LS_HALFWORD_U: dcache_req_o.store_width = HW;
                LS_WORD, LS_WORD_U:         dcache_req_o.store_width = W;
                LS_DOUBLEWORD:              dcache_req_o.store_width = DW;
            default: dcache_req_o.store_width = DW;
        endcase
    end 
    assign dcache_req_o.lsq_addr        = dcachemux_dcache_idx;
    assign dcache_req_o.valid           = dcachearb_dcache_valid;

    // l1dc_lsq_ans_t/l1dc_lsq_wup_t
    assign dcache_dcachedec_ans_valid   = dcache_ans_i.valid;
    assign dcache_dcachedec_wup_valid   = dcache_wup_i.valid;
    always_comb begin
        if (dcache_wup_i.valid) begin
            dcache_lsb_value            = 0;
            dcache_lsb_idx              = 0;
            dcache_lsb_paddr            = { {XLEN-DCACHE_L1_TAG_A_LEN-DCACHE_L1_IDX_A_LEN{1'b0}}, dcache_wup_i.line_addr};
            //dcache_lsb_paddr            = { {XLEN-DCACHE_L1_TAG_A_LEN-DCACHE_L1_IDX_A_LEN-DCACHE_L1_WORD_A_LEN-DCACHE_L1_LINE_OFF_A_LEN{1'b0}}, dcache_wup_i.line_addr, {DCACHE_L1_WORD_A_LEN+DCACHE_L1_LINE_OFF_A_LEN{1'b0}}};
        end else begin
            dcache_lsb_value            = dcache_ans_i.data;
            dcache_lsb_idx              = dcache_ans_i.lsq_addr;
            dcache_lsb_paddr            = 0;
        end
        dcache_dcachedec_is_store       = dcache_ans_i.was_store;
    end

    // -----------------
    // DCACHE HS ARBITER
    // -----------------

    assign dcache_dcachearb_ready = dcache_ready_i;

    `ifdef ENABLE_STORE_PRIO_2WAY_ARBITER
    // The store buffer, connected to valid_i[0] is given higher priority than the load buffer. This should increase the hit ratio of the store to load forwarding. However, it increases the load execution latency. Depending on the scenario, performance may be better or worse than the fair arbiter
    prio_2way_arbiter dcache_hs_arbiter (
        .valid_i        ({ lb_dcachearb_valid, sb_dcachearb_valid }),
        .ready_i        (dcache_dcachearb_ready),
        .valid_o        (dcachearb_dcache_valid),
        .ready_o        ({ dcachearb_lb_ready, dcachearb_sb_ready }),
        .select_o       (dcachemux_sel) // 1 if load buffer is served
    );
    `else
    fair_2way_arbiter dcache_hs_arbiter (
        .clk_i          (clk_i),
        .rst_n_i        (rst_n_i),
        .valid_i        ({ lb_dcachearb_valid, sb_dcachearb_valid }),
        .ready_i        (dcache_dcachearb_ready),
        .valid_o        (dcachearb_dcache_valid),
        .ready_o        ({ dcachearb_lb_ready, dcachearb_sb_ready }),
        .select_o       (dcachemux_sel) // 1 if load buffer is served
    );
    `endif

    // ----------
    // DCACHE MUX
    // ----------
    always_comb begin: dcache_mux
        if (dcachemux_sel) begin
            dcachemux_dcache_isstore    = lb_dcachemux_isstore;
            dcachemux_dcache_paddr      = lb_dcachemux_paddr;
            dcachemux_dcache_value      = 0;                    // only needed for type conversion
            dcachemux_dcache_idx        = { {(BUFF_IDX_LEN-LDBUFF_IDX_LEN){1'b0}}, lb_dcachemux_idx }; // padd with zeroes if the load buffer is smaller than the store buffer
            dcachemux_dcache_sttype     = LS_DOUBLEWORD;
        end else begin
            dcachemux_dcache_isstore    = sb_dcachemux_isstore;
            dcachemux_dcache_paddr      = sb_dcachemux_paddr;
            dcachemux_dcache_value      = sb_dcachemux_value;
            dcachemux_dcache_idx        = { {(BUFF_IDX_LEN-STBUFF_IDX_LEN){1'b0}}, sb_dcachemux_idx }; // padd with zeroes if the load buffer is smaller than the store buffer
            dcachemux_dcache_sttype     = sb_dcachemux_sttype;
        end
    end

    // ---------------
    // DCACHE HS DECODER
    // ---------------
    always_comb begin: dcache_hs_decoder
        if (dcache_dcachedec_is_store) begin
            dcachedec_lb_ans_valid  = 1'b0;
            dcachedec_lb_wup_valid  = 1'b0;    
            dcachedec_sb_ans_valid  = dcache_dcachedec_ans_valid;
            dcachedec_sb_wup_valid  = dcache_dcachedec_wup_valid;
            dcachedec_dcache_ready  = sb_dcachedec_ready;
        end else begin
            dcachedec_lb_ans_valid  = dcache_dcachedec_ans_valid;
            dcachedec_lb_wup_valid  = dcache_dcachedec_wup_valid;
            dcachedec_sb_ans_valid  = 1'b0;
            dcachedec_sb_wup_valid  = 1'b0;    
            dcachedec_dcache_ready  = lb_dcachedec_ready;
        end
    end
    
endmodule
