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
// File: load_buffer.sv
// Author: Michele Caon
// Date: 24/10/2019


import len5_pkg::XLEN;
import len5_pkg::I_IMM;
import len5_pkg::LDBUFF_DEPTH;

import expipe_pkg::*;

// import memory_pkg::VPN_LEN;
// import memory_pkg::PPN_LEN;
// import memory_pkg::VADDR_LEN;
// import memory_pkg::PADDR_LEN;
// import memory_pkg::PAGE_OFFSET_LEN;
// import memory_pkg::exception_e;
// import memory_pkg::NoException;
// import memory_pkg::PageFault;
// import memory_pkg::AccessException;
import memory_pkg::*;

import csr_pkg::satp_mode_t;
import csr_pkg::BARE; 
import csr_pkg::SV39;
import csr_pkg::SV48;

module load_buffer 
(
    input   logic                       clk_i,
    input   logic                       rst_n_i,
    input   logic                       flush_i,
	// input logic stall,

    input   satp_mode_t                 vm_mode_i,      // virtual memory MODE (from the 'satp' CSR)

    // Handshake from/to issue logic
    input   logic                       issue_logic_valid_i,
    output  logic                       issue_logic_ready_o,

    // Data from the decode stage
    input   ldst_type_t                 load_type_i,
    input   logic                       rs1_ready_i,    // first operand already fetched from RF/ROB
    input   logic [ROB_IDX_LEN-1:0]     rs1_idx_i,
    input   logic [XLEN-1:0]            rs1_value_i,
    input   logic [I_IMM-1:0]           imm_value_i,    // The immediate field of the load instruction
    input   logic [ROB_IDX_LEN-1:0]     dest_idx_i,

    // Handshake from/to the virtual address adder
    input   logic                       vadder_valid_i,
    input   logic                       vadder_ready_i,
    output  logic                       vadder_valid_o,
    output  logic                       vadder_ready_o,

    // Data from/to the virtual address adder
    input   logic [XLEN-1:0]            vadder_vaddr_i,
    input   logic [LDBUFF_IDX_LEN-1:0]  vadder_idx_i,
    input   vadder_except_t             vadder_except_i, // LD_ADDR_MISALIGNED or LD_PAGE_FAULT exceptions
    output  logic                       vadder_isstore_o,
    output  logic [XLEN-1:0]            rs1_value_o,
    output  logic [I_IMM-1:0]           imm_value_o,
    output  logic [LDBUFF_IDX_LEN-1:0]  vadder_idx_o,
    output  ldst_type_t                 vadder_ldtype_o,

    // Handshake from/to the TLB
    input   logic                       dtlb_wu_valid_i,
    input   logic                       dtlb_ans_valid_i,
    input   logic                       dtlb_ready_i,
    output  logic                       dtlb_valid_o, 
    output  logic                       dtlb_ready_o, //

    // Data from/to the TLB
    input   logic [VPN_LEN-1:0]         dtlb_vaddr_i,
    input   logic [PPN_LEN-1:0]         dtlb_ppn_i,
    input   exception_e                 dtlb_except_i,
    input   logic [LDBUFF_IDX_LEN-1:0]  dtlb_idx_i,
    output  logic                       dtlb_isstore_o,
    output  logic [VPN_LEN-1:0]         dtlb_vaddr_o,
    output  logic [LDBUFF_IDX_LEN-1:0]  dtlb_idx_o,

    // Handshake from/to the D$
    input   logic                       dcache_wu_valid_i,
    input   logic                       dcache_ans_valid_i,
    input   logic                       dcache_ready_i,
    output  logic                       dcache_valid_o,
    output  logic                       dcache_ready_o, //

    // Data from/to the D$
    input   logic [DCACHE_L1_LINE_A_LEN-1:0] dcache_lineaddr_i,
    input   logic [XLEN-1:0]            dcache_value_i,
    input   logic [LDBUFF_IDX_LEN-1:0]  dcache_idx_i,
    output  logic                       dcache_isstore_o,
    output  logic [XLEN-1:0]            dcache_paddr_o,
    output  logic [LDBUFF_IDX_LEN-1:0]  dcache_idx_o,

    // Data from/to the store buffer
    input   logic [STBUFF_IDX_LEN:0]    inflight_store_cnt_i, // number of uncommitted store instructions in the store buffer
    input   logic                       store_committing_i, // A store is committing in the store buffer
    input   logic                       vfwd_hit_i,
    input   logic                       vfwd_depfree_i,
    input   logic                       pfwd_hit_i,
    input   logic                       pfwd_depfree_i,
    input   logic [XLEN-1:0]            vfwd_value_i,
    input   logic [XLEN-1:0]            pfwd_value_i,
    output  logic [XLEN-1:0]            vfwd_vaddr_o,
    output  logic [XLEN-1:0]            pfwd_paddr_o,
    output  ldst_type_t                 vfwd_ldtype_o,
    output  ldst_type_t                 pfwd_ldtype_o,
    output  logic [STBUFF_IDX_LEN:0]    vfwd_older_stores_o,
    output  logic [STBUFF_IDX_LEN:0]    pfwd_older_stores_o,

    // Hanshake from/to the CDB 
    input   logic                       cdb_ready_i,
    input   logic                       cdb_valid_i,    // to know if the CDB is carrying valid data
    output  logic                       cdb_valid_o,

    // Data from/to the CDB
    input   logic [ROB_IDX_LEN-1:0]     cdb_idx_i,
    input   logic [XLEN-1:0]            cdb_data_i,
    input   logic                       cdb_except_raised_i,
    output  logic [ROB_IDX_LEN-1:0]     cdb_idx_o,
    output  logic [XLEN-1:0]            cdb_data_o,
    output  logic                       cdb_except_raised_o,
    output  logic [ROB_EXCEPT_LEN-1:0]  cdb_except_o
);

    // DEFINITIONS

    // Load buffer pointers
    logic [LDBUFF_IDX_LEN-1:0]      new_idx, vadder_req_idx, dtlb_req_idx, dcache_req_idx, cdb_req_idx; // next free entry, entry selected for virtual address computation, for TLB access and for D$ access
    logic                           new_idx_valid, vadder_idx_valid, dtlb_idx_valid, dcache_idx_valid, cdb_idx_valid; // the selector encoded output is valid

    // Forwarding indexes
    logic vfwd_idx_reg_en;
    logic [LDBUFF_IDX_LEN-1:0]      vfwd_idx, pfwd_idx;
    logic                           pfwd_idx_valid;

    // Operation control
    logic                           lb_insert, lb_vadder_req, lb_vadder_ans, lb_dtlb_req, lb_dtlb_wu, lb_dtlb_ans, lb_dcache_req, lb_dcache_wu, lb_dcache_ans, lb_pop, vfwd_req, pfwd_req;

    // Input data doubleword (from D$, virtual forwarding or physical forwarding)
    logic [XLEN-1:0]                dcache_value; 

    // The load buffer data structure
    lb_entry_t                      lb_data[LDBUFF_DEPTH-1:0];

    // Status signals
    logic [LDBUFF_DEPTH-1:0]        valid_a, busy_a, store_dep_a, pfwd_attempted_a, no_older_stores_a, rs1_ready_a, vaddr_ready_a, paddr_ready_a, except_raised_a, completed_a;
    `ifdef ENABLE_AGE_BASED_SELECTOR
    logic [ROB_IDX_LEN-1:0]         entry_age_a [0:LDBUFF_DEPTH-1];
    `endif
    
    // Complete physical address
    logic [XLEN-1:0]                paddr_a [0:LDBUFF_DEPTH-1];

    //--------------------------\\
    //----- STATUS SIGNALS -----\\
    //--------------------------\\
    // These are required because name selection after indexing is not supported
    always_comb begin: status_signals_gen
        for (int i = 0; i < LDBUFF_DEPTH; i++) begin
            valid_a[i]              = lb_data[i].valid;
            busy_a[i]               = lb_data[i].busy;
            store_dep_a[i]          = lb_data[i].store_dep;
            no_older_stores_a[i]    = (lb_data[i].older_stores == 0) ? 1'b1 : 1'b0;
            rs1_ready_a[i]          = lb_data[i].rs1_ready;
            vaddr_ready_a[i]        = lb_data[i].vaddr_ready;
            paddr_ready_a[i]        = lb_data[i].paddr_ready;
            except_raised_a[i]      = lb_data[i].except_raised;
            completed_a[i]          = lb_data[i].completed;
            pfwd_attempted_a[i]     = lb_data[i].pfwd_attempted;
            `ifdef ENABLE_AGE_BASED_SELECTOR
            entry_age_a[i]          = lb_data[i].entry_age;
            `endif
        end
    end

    //-------------------------------------\\
    //----- COMPLETE PHYSICAL ADDRESS -----\\
    //-------------------------------------\\
    always_comb begin: paddr_gen
        for (int i = 0; i < LDBUFF_DEPTH; i++) begin
            paddr_a[i] = { {(XLEN-PADDR_LEN){1'b0}}, lb_data[i].ppn, lb_data[i].vaddr[PAGE_OFFSET_LEN-1:0] };
        end
    end

    //-------------------------------------\\
    //----- LOAD BUFFER CONTROL LOGIC -----\\
    //-------------------------------------\\
    // Generates the control signals that trigger specific operations on the data structure based in input and status signals.
    always_comb begin: lb_control_logic
        // DEFAULT VALUES
        // Operation control
        lb_insert           = 1'b0;
        lb_pop              = 1'b0;
        
        lb_vadder_req       = 1'b0;
        lb_vadder_ans       = 1'b0;
        
        lb_dtlb_req         = 1'b0;
        lb_dtlb_wu          = 1'b0;
        lb_dtlb_ans         = 1'b0;
        
        lb_dcache_req       = 1'b0;
        lb_dcache_wu        = 1'b0;
        lb_dcache_ans       = 1'b0;

        // Handshake control
        issue_logic_ready_o     = 1'b0;
        
        vadder_valid_o      = 1'b0;
        vadder_ready_o      = 1'b1;     // Always ready to accept the computed virtual address
        
        dtlb_valid_o        = 1'b0;
        dtlb_ready_o        = 1'b1;     // Always ready to accept the physical address
        
        dcache_valid_o      = 1'b0;
        dcache_ready_o      = 1'b1;     // Always ready to accept data
        
        cdb_valid_o         = 1'b0;

        // Forwarding control
        vfwd_idx_reg_en     = 1'b0;
        vfwd_req            = 1'b0;
        pfwd_req            = 1'b0;

        // INSERT NEW INSTRUCTION
        // Insert a new instruction in the queue if the selected entry is empty (i.e. not valid) and the decoder is sending a valid instruction to the load buffer
        if (!lb_data[new_idx].valid && new_idx_valid) begin
            issue_logic_ready_o = 1'b1;
            if (issue_logic_valid_i) lb_insert = 1'b1;
        end 

        // REQUEST TO THE VIRTUAL ADDRESS ADDER
        // The selected entry must be valid (other checks are performed by the selector)
        if (lb_data[vadder_req_idx].valid && vadder_idx_valid/*&&!(stall)*/) begin
            vadder_valid_o  = 1'b1;
            if (vadder_ready_i) lb_vadder_req = 1'b1; // The adder accepted the request, and the entry is marked as busy
        end

        // REQUEST TO THE TLB
        // The selected entry must be valid (other checks are performed by the selector)
        if (lb_data[dtlb_req_idx].valid && dtlb_idx_valid/*&&!(stall)*/) begin
            dtlb_valid_o    = 1'b1;
            if (dtlb_ready_i) lb_dtlb_req = 1'b1; // The TLB accepted the request, so the entry can be marked as busy
        end

        // REQUEST TO THE D$
        // The selected entry must be valid (other checks are performed by the selector)
        if (lb_data[dcache_req_idx].valid && dcache_idx_valid/*&&!(stall)*/) begin
            dcache_valid_o  = 1'b1;
            if (dcache_ready_i) lb_dcache_req = 1'b1; // the D$ can accept the request
        end

        // REQUEST TO THE CDB
        // The selected entry must be valid (other checks are performed by the selector)
        if (lb_data[cdb_req_idx].valid && cdb_idx_valid/*&&!(stall)*/) begin
            cdb_valid_o     = 1'b1;
            if (cdb_ready_i) lb_pop = 1'b1;
        end

        // FORWARD ON VIRTUAL ADDRESS
        if (lb_data[vfwd_idx].valid && lb_data[vfwd_idx].busy && !lb_data[vfwd_idx].completed && lb_data[vfwd_idx].vaddr_ready && !lb_data[vfwd_idx].except_raised && !lb_data[vfwd_idx].paddr_ready/*&&!(stall)*/) begin
            vfwd_req        = 1'b1;
        end

        // FORWARD ON PHYSICAL ADDRESS
        if (lb_data[pfwd_idx].valid && pfwd_idx_valid/*&&!(stall)*/) begin 
            pfwd_req        = 1'b1;
        end

        //-------------------\\
        //----- ANSWERS -----\\
        //-------------------\\

        // VIRTUAL ADDRESS ADDER ANSWER
        if (vadder_valid_i) begin
            lb_vadder_ans   = 1'b1;
            vfwd_idx_reg_en = 1'b1; // Enable forwarding index register
        end 

        // TLB ANSWER/WAKE-UP
        if (dtlb_wu_valid_i) begin
            lb_dtlb_wu      = 1'b1;
        end 
        if (dtlb_ans_valid_i) begin
            lb_dtlb_ans     = 1'b1;
        end

        // D$ ANSWER/WAKE-UP
        if (dcache_wu_valid_i) begin
            lb_dcache_wu    = 1'b1;
        end 
        if (dcache_ans_valid_i) begin
            lb_dcache_ans   = 1'b1;
        end

    end 

    //-----------------------------------\\
    //----- LOAD BUFFER DATA UPDATE -----\\
    //-----------------------------------\\
    always_ff @(posedge clk_i or negedge rst_n_i) begin: lb_data_update
        if (!rst_n_i) begin // Asynchronous reset
            foreach (lb_data[i]) begin
                lb_data[i] <= 0;
            end
        end else if (flush_i) begin // Synchronous flush: clering status fields is enough
            foreach (lb_data[i]) begin
                lb_data[i].valid            <= 1'b0;
                lb_data[i].busy             <= 1'b0;
                lb_data[i].store_dep        <= 1'b0;
                lb_data[i].older_stores     <= 'b0;
                lb_data[i].rs1_ready        <= 1'b0;
                lb_data[i].vaddr_ready      <= 1'b0;
                lb_data[i].paddr_ready      <= 1'b0;
                lb_data[i].completed        <= 1'b0;
                lb_data[i].except_raised    <= 1'b0;
            end
        end else begin 

            //-------------------------------\\
            //----- PARALLEL OPERATIONS -----\\
            //-------------------------------\\

            foreach (lb_data[i]) begin
        
                // RETRIEVE BASE ADDRESS FROM THE CDB (parallel access port on rs1_value field)
                if (lb_data[i].valid && !lb_data[i].rs1_ready) begin
                    if (cdb_valid_i && !cdb_except_raised_i && (lb_data[i].rs1_idx == cdb_idx_i)) begin
                        lb_data[i].rs1_ready <= 1'b1;
                        lb_data[i].rs1_value <= cdb_data_i;
                    end
                end
                
                // DECREMENT THE UNCOMMITTED STORES COUNTERS EACH TIME A STORE COMMITS
                if (lb_data[i].valid && store_committing_i && (lb_data[i].older_stores != 0)) lb_data[i].older_stores <= lb_data[i].older_stores - 1;
        
                // TLB WAKE UP
                if (lb_dtlb_wu) begin
                    if (lb_data[i].valid && lb_data[i].busy && !lb_data[i].paddr_ready && (lb_data[i].vaddr[VADDR_LEN-1:PAGE_OFFSET_LEN] == dtlb_vaddr_i)) begin
                        // Exception handling
                        case(dtlb_except_i)
                            PageFault: begin
                                lb_data[i].busy             <= 1'b0; 
                                lb_data[i].except_raised    <= 1'b1;
                                lb_data[i].except_code      <= E_LD_PAGE_FAULT;
                                lb_data[i].ld_value         <= lb_data[i].vaddr; // copy the offending virtual address in the result field so it can be used during exception handling
                                lb_data[i].completed        <= 1'b1;        // mark the entry as completed so the cache access is skipped
                            end
                            AccessException: begin
                                lb_data[i].busy             <= 1'b0; 
                                lb_data[i].except_raised    <= 1'b1;
                                lb_data[i].except_code      <= E_LD_ACCESS_FAULT;
                                lb_data[i].ld_value         <= lb_data[i].vaddr; // copy the offending virtual address in the result field so it can be used during exception handling
                                lb_data[i].completed        <= 1'b1;        // mark the entry as completed so the cache access is skipped
                            end
                            NoException: begin // normal execution
                                lb_data[i].busy             <= 1'b0;        // clear busy bit so the entry can proceed to cache access
                                lb_data[i].paddr_ready      <= 1'b1;
                                lb_data[i].ppn              <= dtlb_ppn_i; 
                            end
                            default: begin
                                lb_data[i].busy             <= 1'b0;        // clear busy so vaddr forwarding is skipped
                                lb_data[i].except_raised    <= 1'b1;		// This is in case the default happens, which is not ok since it should not occur in normal situations
                                lb_data[i].except_code      <= E_UNKNOWN;   // reserved code 10
                                lb_data[i].ld_value         <= lb_data[i].vaddr;
                                lb_data[i].completed        <= 1'b1;
                            end
                        endcase
                    end
                end

                // D$ WAKE UP
                if (lb_dcache_wu) begin
                    if (lb_data[i].valid && lb_data[i].paddr_ready && (paddr_a[i][XLEN-1:(DCACHE_L1_WORD_A_LEN+DCACHE_L1_LINE_OFF_A_LEN)] == dcache_lineaddr_i)) begin
                        lb_data[i].busy <= 1'b0; // clear the busy bit so the instruction can be replayed
                    end
                end

            end
            
            //----------------------------\\
            //----- WRITE OPERATIONS -----\\
            //----------------------------\\
            
            // INSERT NEW INSTRUCTION
            if (lb_insert) begin
                lb_data[new_idx].valid          <= issue_logic_valid_i;
                lb_data[new_idx].busy           <= 1'b0;
                lb_data[new_idx].store_dep      <= 1'b0;
                `ifdef ENABLE_AGE_BASED_SELECTOR
                lb_data[new_idx].entry_age      <= 0;
                `endif
                lb_data[new_idx].older_stores   <= inflight_store_cnt_i;
                lb_data[new_idx].load_type      <= load_type_i;
                lb_data[new_idx].rs1_ready      <= rs1_ready_i;
                lb_data[new_idx].rs1_idx        <= rs1_idx_i;
                lb_data[new_idx].rs1_value      <= rs1_value_i;
                lb_data[new_idx].imm_value      <= imm_value_i;
                lb_data[new_idx].vaddr_ready    <= 1'b0;
                lb_data[new_idx].paddr_ready    <= 1'b0;
                lb_data[new_idx].dest_idx       <= dest_idx_i;
                lb_data[new_idx].except_raised  <= 1'b0;
                lb_data[new_idx].completed      <= 1'b0;

                `ifdef ENABLE_AGE_BASED_SELECTOR
                // Update the age of all valid entries
                foreach(lb_data[i]) begin
                    if (new_idx != i[LDBUFF_IDX_LEN-1:0] && lb_data[i].valid) lb_data[i].entry_age <= lb_data[i].entry_age + 1;
                end
                `endif
            end

            // REQUEST TO THE VIRTUAL ADDRESS ADDER
            if (lb_vadder_req) begin
                lb_data[vadder_req_idx].busy    <= 1'b1;
            end

            // REQUEST TO THE TLB
            if (lb_dtlb_req) begin
                lb_data[dtlb_req_idx].busy      <= 1'b1;
            end

            // REQUEST TO THE D$
            if (lb_dcache_req) begin
                lb_data[dcache_req_idx].busy    <= 1'b1;
            end

            // REQUEST TO THE CDB
            if (lb_pop) begin
                lb_data[cdb_req_idx].valid      <= 1'b0; // Pop the entry sent to the CDB
            end

            // FORWARD ON VIRTUAL ADDRESS
            // Clear busy bits is forwarding has already finished
            if (lb_data[vfwd_idx].valid && lb_data[vfwd_idx].busy) lb_data[vfwd_idx].busy <= 1'b0;

            // FORWARD ON PHYSICAL ADDRESS
            // Clear busy bits is forwarding has already finished
            if (pfwd_req) begin
                lb_data[pfwd_idx].pfwd_attempted <= 1'b1; 
            end

            //----------------------------------------------\\
            //----- PROCESS ANSWERS ON DIFFERENT PORTS -----\\
            //----------------------------------------------\\

            // VIRTUAL ADDRESS ADDER ANSWER (WRITE PORT 1: entry.vaddr, entry.value)

            if (lb_vadder_ans) begin
                // Exception handling
                case(vadder_except_i)
                    VADDER_ALIGN_EXCEPT: begin
                        lb_data[vadder_idx_i].busy          <= 1'b0; // clear busy so vaddr forwarding is skipped
                        lb_data[vadder_idx_i].except_raised <= 1'b1;
                        lb_data[vadder_idx_i].except_code   <= E_LD_ADDR_MISALIGNED;
                        lb_data[vadder_idx_i].ld_value      <= vadder_vaddr_i; // The virtual address is copied in the result field instead of the loaded value, so it will be sent to the CDB (i.e. the ROB)
                        lb_data[vadder_idx_i].completed     <= 1'b1; // Mark the entry as completed so TLB and D$ accesses are skipped
                    end
                    VADDER_PAGE_EXCEPT: begin
                        lb_data[vadder_idx_i].busy          <= 1'b0; // clear busy so vaddr forwarding is skipped
                        lb_data[vadder_idx_i].except_raised <= 1'b1;
                        lb_data[vadder_idx_i].except_code   <= E_LD_PAGE_FAULT;
                        lb_data[vadder_idx_i].ld_value      <= vadder_vaddr_i; // The virtual address is copied in the result field so it will be sent to the CDB (i.e. the ROB)
                        lb_data[vadder_idx_i].completed     <= 1'b1; // Mark the entry as completed so TLB and D$ accesses are skipped
                    end
                    VADDER_NO_EXCEPT: begin
                        // If virtual memory is not enabled, save the virtual address in the physical address field and skip vaddr forwarding by clearing the busy bit.
                        if (vm_mode_i == BARE) begin
                            lb_data[vadder_idx_i].busy      <= 1'b0;
                            lb_data[vadder_idx_i].paddr_ready <= 1'b1;
                            lb_data[vadder_idx_i].ppn       <= vadder_vaddr_i[PADDR_LEN-1:PAGE_OFFSET_LEN];
                        end
                        lb_data[vadder_idx_i].vaddr_ready   <= 1'b1; // the virtual address is available
                        lb_data[vadder_idx_i].vaddr         <= vadder_vaddr_i; // the virtual address is copied in the entry
                    end
                    default: begin // unknown exception
                        lb_data[vadder_idx_i].busy          <= 1'b0; // clear busy so vaddr forwarding is skipped
                        lb_data[vadder_idx_i].except_raised <= 1'b1;
                        lb_data[vadder_idx_i].except_code   <= E_UNKNOWN; // reserved code 10
                        lb_data[vadder_idx_i].ld_value      <= vadder_vaddr_i;
                        lb_data[vadder_idx_i].completed     <= 1'b1;
                    end
                endcase
            end

            // TLB ANSWER (WRITE PORT 2: entry.ppn, entry.value)

            if (lb_dtlb_ans) begin
                // Exception handling
                case(dtlb_except_i)
                    PageFault: begin
                        lb_data[dtlb_idx_i].busy            <= 1'b0; 
                        lb_data[dtlb_idx_i].except_raised   <= 1'b1;
                        lb_data[dtlb_idx_i].except_code     <= E_LD_PAGE_FAULT;
                        lb_data[dtlb_idx_i].ld_value        <= lb_data[dtlb_idx_i].vaddr; // copy the offending virtual address in the result field so it can be used during exception handling
                        lb_data[dtlb_idx_i].completed       <= 1'b1; // mark the entry as completed so the cache access is skipped
                    end
                    AccessException: begin
                        lb_data[dtlb_idx_i].busy            <= 1'b0; 
                        lb_data[dtlb_idx_i].except_raised   <= 1'b1;
                        lb_data[dtlb_idx_i].except_code     <= E_LD_ACCESS_FAULT;
                        lb_data[dtlb_idx_i].ld_value        <= lb_data[dtlb_idx_i].vaddr; // copy the offending virtual address in the result field so it can be used during exception handling
                        lb_data[dtlb_idx_i].completed       <= 1'b1; // mark the entry as completed so the cache access is skipped
                    end
                    NoException: begin // normal execution
                        lb_data[dtlb_idx_i].busy            <= 1'b0; // clear busy bit so the entry can proceed to cache access
                        lb_data[dtlb_idx_i].paddr_ready     <= 1'b1;
                        lb_data[dtlb_idx_i].ppn             <= dtlb_ppn_i; // last 12 bits are not translated
                    end
                    default: begin
                        lb_data[dtlb_idx_i].busy            <= 1'b0; // clear busy so vaddr forwarding is skipped
                        lb_data[dtlb_idx_i].except_raised   <= 1'b1;
                        lb_data[dtlb_idx_i].except_code     <= E_UNKNOWN; // reserved code 10
                        lb_data[dtlb_idx_i].ld_value        <= lb_data[dtlb_idx_i].vaddr;
                        lb_data[dtlb_idx_i].completed       <= 1'b1;
                    end
                endcase
            end

            // D$ ANSWER (WRITE PORT 3: entry.value)
            if (lb_dcache_ans) begin
                lb_data[dcache_idx_i].busy                  <= 1'b0; // clear the busy bit
                lb_data[dcache_idx_i].ld_value              <= dcache_value;
                lb_data[dcache_idx_i].completed             <= 1'b1; // mark instruction as completed
            end

            // VIRTUAL ADDRESS FORWARDING (WRITE PORT 4: entry.value)
            if (vfwd_req) begin // only if vfwd is being attempted
                if (vfwd_hit_i) begin
                    lb_data[vfwd_idx].ld_value              <= vfwd_value_i;
                    lb_data[vfwd_idx].completed             <= 1'b1;
                end else if (vfwd_depfree_i) begin
                    lb_data[vfwd_idx].older_stores          <= 0;
                end else begin
                    lb_data[vfwd_idx].store_dep             <= 1'b1;
                end
            end

            // PHYSICAL ADDRESS FORWARDING (WRITE PORT 5: entry.value)
            if (pfwd_req) begin // only if pfwd is being attempted
                if (pfwd_hit_i) begin
                    lb_data[pfwd_idx].ld_value              <= pfwd_value_i;
                    lb_data[pfwd_idx].completed             <= 1'b1;
                end else if (pfwd_depfree_i) begin
                    lb_data[pfwd_idx].older_stores          <= 0;
                end else begin
                    lb_data[pfwd_idx].store_dep             <= 1'b1;
                end
            end
        end
    end

    //------------------------------\\
    //----- NEW ENTRY SELECTOR -----\\
    //------------------------------\\
    // Selects the entry where the next issued instruction will be inserted. It is the first empty (i.e. not valid) entry in the queue, selected by a priority encoder.
    prio_enc #(.N(LDBUFF_DEPTH)) new_entry_selector
    (
        .lines_i    (~valid_a),
        .enc_o      (new_idx),
        .valid_o    (new_idx_valid)
    );

    //------------------------------------------------\\
    //----- VIRTUAL ADDRESS COMPUTATION SELECTOR -----\\
    //------------------------------------------------\\
    `ifdef ENABLE_AGE_BASED_SELECTOR
    // The selector follows a "first come first served" scheduling policy. The oldest valid entry whose base address from rs1 is available and whose virtual address hasn't been computed yet (vaddr_ready = 0) is selected to be sent to the virtual address adder
    age_based_sel #(.N(LDBUFF_DEPTH), .AGE_LEN(ROB_IDX_LEN)) vaddr_req_selector
    (
        .lines_i    (valid_a & ~busy_a & rs1_ready_a & ~vaddr_ready_a & ~completed_a),
        .ages_i     (entry_age_a),
        .enc_o      (vadder_req_idx),
        .valid_o    (vadder_idx_valid)
    );
    `else
    // Simple priority encoder
    prio_enc #(.N(LDBUFF_DEPTH)) vaddr_req_selector
    (
        .lines_i    (valid_a & ~busy_a & rs1_ready_a & ~vaddr_ready_a & ~completed_a),
        .enc_o      (vadder_req_idx),
        .valid_o    (vadder_idx_valid)
    );
    `endif

    //-------------------------------\\
    //----- TLB ACCESS SELECTOR -----\\
    //-------------------------------\\
    `ifdef ENABLE_AGE_BASED_SELECTOR
    // The selector follows a "first come first served" scheduling policy. The oldest valid entry whose virtual address has already be computed and that's not busy or completed (thanks to forwarding) is selected for the address translation
    age_based_sel #(.N(LDBUFF_DEPTH), .AGE_LEN(ROB_IDX_LEN)) dtlb_req_selector
    (
        .lines_i    (valid_a & ~busy_a & vaddr_ready_a & ~paddr_ready_a & ~except_raised_a & ~completed_a),
        .ages_i     (entry_age_a),
        .enc_o      (dtlb_req_idx),
        .valid_o    (dtlb_idx_valid)
    );
    `else
    // Simple priority encoder
    prio_enc #(.N(LDBUFF_DEPTH)) dtlb_req_selector
    (
        .lines_i    (valid_a & ~busy_a & vaddr_ready_a & ~paddr_ready_a & ~except_raised_a & ~completed_a),
        .enc_o      (dtlb_req_idx),
        .valid_o    (dtlb_idx_valid)
    );
    `endif

    //------------------------------------------------\\
    //----- PHYSICAL ADDRESS FORWARDING SELECTOR -----\\
    //------------------------------------------------\\
    `ifdef ENABLE_AGE_BASED_SELECTOR
    // The selector follows a "first come first served" scheduling policy. In order to be selcted, an instruction must be valid, not busy or completed, have its paddr ready, no exceptions registered and no physical forwarding attempted.
    age_based_sel #(.N(LDBUFF_DEPTH), .AGE_LEN(ROB_IDX_LEN)) pfwd_req_selector
    (
        .lines_i    (valid_a & ~busy_a & paddr_ready_a & ~completed_a & ~except_raised_a & ~pfwd_attempted_a),
        .ages_i     (entry_age_a),
        .enc_o      (pfwd_idx),
        .valid_o    (pfwd_idx_valid)
    );
    `else
    // Simple priority encoder
    prio_enc #(.N(LDBUFF_DEPTH)) pfwd_req_selector
    (
        .lines_i    (valid_a & ~busy_a & paddr_ready_a & ~completed_a & ~except_raised_a & ~pfwd_attempted_a),
        .enc_o      (pfwd_idx),
        .valid_o    (pfwd_idx_valid)
    );
    `endif

    //--------------------------------------\\
    //----- DATA CACHE ACCESS SELECTOR -----\\
    //--------------------------------------\\
    `ifdef ENABLE_AGE_BASED_SELECTOR
    // The selector follows a "first come first served" scheduling policy. The oldest valid entry whose physical address has already be computed and that's not busy or completed (thanks to forwarding) is selected for the cache access
    age_based_sel #(.N(LDBUFF_DEPTH), .AGE_LEN(ROB_IDX_LEN)) dcache_req_selector
    (
        .lines_i    (valid_a & ~busy_a & ~completed_a & paddr_ready_a & ~except_raised_a & pfwd_attempted_a & (~store_dep_a | no_older_stores_a)),
        .ages_i     (entry_age_a),
        .enc_o      (dcache_req_idx),
        .valid_o    (dcache_idx_valid)
    );
    `else
    // Simple priority encoder
    prio_enc #(.N(LDBUFF_DEPTH)) dcache_req_selector
    (
        .lines_i    (valid_a & ~busy_a & ~completed_a & paddr_ready_a & ~except_raised_a & pfwd_attempted_a & (~store_dep_a | no_older_stores_a)),
        .enc_o      (dcache_req_idx),
        .valid_o    (dcache_idx_valid)
    );
    `endif

    //------------------------\\
    //----- CDB SELECTOR -----\\
    //------------------------\\
    `ifdef ENABLE_AGE_BASED_SELECTOR
    // The selector follows a "first come first served" scheduling policy. The oldest valid entry that has already completed (by forwarding, cache access or exception raising) is selected to write its data on the CDB, as soon as it becomes available
    age_based_sel #(.N(LDBUFF_DEPTH), .AGE_LEN(ROB_IDX_LEN)) cdb_req_selector
    (
        .lines_i    (valid_a & completed_a),
        .ages_i     (entry_age_a),
        .enc_o      (cdb_req_idx),
        .valid_o    (cdb_idx_valid)
    );
    `else
    // Simple priority encoder
    prio_enc #(.N(LDBUFF_DEPTH)) cdb_req_selector
    (
        .lines_i    (valid_a & completed_a),
        .enc_o      (cdb_req_idx),
        .valid_o    (cdb_idx_valid)
    );
    `endif

    //-------------------------------------\\
    //----- FORWARDING INDEX REGISTER -----\\
    //-------------------------------------\\
    // When the virtual address adder returns the computed virtual address or and the index of the corresponding entry of the load buffer, this index is saved in a register so it can be used in the next cycle to select the entry for virtual address forwarding
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) vfwd_idx <= 0;
        else vfwd_idx <= (vfwd_idx_reg_en) ? vadder_idx_i : vfwd_idx;
    end

    //--------------------------\\
    //----- BYTE SELECTORS -----\\
    //--------------------------\\
    // The virtual address adder raises an exception if the load instructions are not aligned. If no exception is detected, the correct set of bytes must be selected and sign extended from the incoming data (D$ or forwarding), according to the load type.

    // FROM THE D$
    byte_selector dcache_byte_selector 
    (
        .type_i     (lb_data[dcache_idx_i].load_type),
        .byte_off   (paddr_a[dcache_idx_i][2:0]),
        .line_i     (dcache_value_i),
        .line_o     (dcache_value)
    );

    //-----------------------------\\
    //----- OUTPUT EVALUATION -----\\
    //-----------------------------\\
    
    // TO THE VIRTUAL ADDRESS ADDER (OPERANDS READ PORT 1)
    assign vadder_isstore_o     = 1'b0;                                 // the instruction is a load
    assign rs1_value_o          = lb_data[vadder_req_idx].rs1_value;
    assign imm_value_o          = lb_data[vadder_req_idx].imm_value;
    assign vadder_idx_o         = vadder_req_idx;
    assign vadder_ldtype_o      = lb_data[vadder_req_idx].load_type;
    
    // TO THE TLB 
    assign dtlb_isstore_o       = 1'b0;                                 // the instruction is a load
    assign dtlb_vaddr_o         = lb_data[dtlb_req_idx].vaddr[VADDR_LEN-1:PAGE_OFFSET_LEN]; // (VADDR READ PORT 1)
    assign dtlb_idx_o           = dtlb_req_idx;

    // TO THE D$ 
    assign dcache_isstore_o     = 1'b0;                                 // the instruction is a load
    assign dcache_paddr_o       = paddr_a[dcache_req_idx];              // (PADDR READ PORT 1)
    assign dcache_idx_o         = dcache_req_idx;

    // TO THE STORE BUFFER
    assign vfwd_vaddr_o         = lb_data[vfwd_idx].vaddr; // (VADDR READ PORT 2)
    assign pfwd_paddr_o         = paddr_a[pfwd_idx]; // (PADDR READ PORT 2)
    assign vfwd_ldtype_o        = lb_data[vfwd_idx].load_type;
    assign pfwd_ldtype_o        = lb_data[pfwd_idx].load_type;
    assign vfwd_older_stores_o  = lb_data[vfwd_idx].older_stores; // (OLDER STORES READ PORT 1)
    assign pfwd_older_stores_o  = lb_data[pfwd_idx].older_stores; // (OLDER STORES READ PORT 2)

    // TO THE CDB
    assign cdb_idx_o            = lb_data[cdb_req_idx].dest_idx;
    assign cdb_data_o           = lb_data[cdb_req_idx].ld_value;
    assign cdb_except_raised_o  = lb_data[cdb_req_idx].except_raised;
    assign cdb_except_o         = { {(ROB_EXCEPT_LEN-EXCEPT_TYPE_LEN){1'b0} }, lb_data[cdb_req_idx].except_code };

    //----------------------\\
    //----- ASSERTIONS -----\\
    //----------------------\\
    `ifndef SYNTHESIS
    always @(negedge clk_i) begin
        // Notice when the load buffer is full
        assert (valid_a !== '1) else $warning("Load buffer full: you might want to increase its depth");
        foreach (lb_data[i]) begin
            assert (lb_data[i].except_code != E_UNKNOWN) else $warning("Load buffer entry %4d has encountered an unknown exception", i);
        end
    end
    `endif

endmodule
