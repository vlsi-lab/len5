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
// File: store_buffer.sv
// Author: Michele Caon
// Date: 27/10/2019


import len5_pkg::XLEN;
import len5_pkg::S_IMM;
import len5_pkg::STBUFF_DEPTH;

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

module store_buffer 
(
    input   logic                       clk_i,
    input   logic                       rst_n_i,
    input   logic                       flush_i,
	//input logic stall,

    input   satp_mode_t                 vm_mode_i,          // virtual memory MODE (from the 'satp' CSR)

    // Handshake from/to issue arbiter
    input   logic                       issue_logic_valid_i,
    output  logic                       issue_logic_ready_o,

    // Data from the decode stage
    input   ldst_type_t                 store_type_i,
    input   logic                       rs1_ready_i,        // first operand already fetched from RF/ROB
    input   logic [ROB_IDX_LEN-1:0]     rs1_idx_i,
    input   logic [XLEN-1:0]            rs1_value_i,
    input   logic                       rs2_ready_i,        // second operand already fetched from RF/ROB
    input   logic [ROB_IDX_LEN-1:0]     rs2_idx_i,
    input   logic [XLEN-1:0]            rs2_value_i,
    input   logic [S_IMM-1:0]           imm_value_i,        // The immediate field of the load instruction
    input   logic [ROB_IDX_LEN-1:0]     dest_idx_i,

    // Handshake from/to the virtual address adder
    input   logic                       vadder_ready_i,
    input   logic                       vadder_valid_i,
    output  logic                       vadder_valid_o,
    output  logic                       vadder_ready_o,

    // Data from/to the virtual address adder
    input   logic [XLEN-1:0]            vadder_vaddr_i,
    input   logic [STBUFF_IDX_LEN-1:0]  vadder_idx_i,
    input   vadder_except_t             vadder_except_i,    // LD_ADDR_MISALIGNED or LD_PAGE_FAULT exceptions
    output  logic                       vadder_isstore_o,
    output  logic [XLEN-1:0]            rs1_value_o,
    output  logic [S_IMM-1:0]           imm_value_o,
    output  logic [STBUFF_IDX_LEN-1:0]  vadder_idx_o,
    output  ldst_type_t                 vadder_sttype_o,

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
    input   logic [STBUFF_IDX_LEN-1:0]  dtlb_idx_i,
    output  logic                       dtlb_isstore_o,
    output  logic [VPN_LEN-1:0]         dtlb_vaddr_o,
    output  logic [STBUFF_IDX_LEN-1:0]  dtlb_idx_o,

    // Handshake from/to the D$
    input   logic                       dcache_wu_valid_i,
    input   logic                       dcache_ans_valid_i,
    input   logic                       dcache_ready_i,
    output  logic                       dcache_valid_o,
    output  logic                       dcache_ready_o, //

    // Data from/to the D$
    input   logic [DCACHE_L1_LINE_A_LEN-1:0] dcache_lineaddr_i,
    input   logic [STBUFF_IDX_LEN-1:0]  dcache_idx_i,
    output  logic                       dcache_isstore_o,
    output  logic [XLEN-1:0]            dcache_paddr_o,
    output  logic [XLEN-1:0]            dcache_value_o,
    output  logic [STBUFF_IDX_LEN-1:0]  dcache_idx_o,
    output  ldst_type_t                 dcache_sttype_o,

    // Data from/to the load buffer
    input   logic [XLEN-1:0]            vfwd_vaddr_i,
    input   logic [XLEN-1:0]            pfwd_paddr_i,
    input   ldst_type_t                 vfwd_ldtype_i,
    input   ldst_type_t                 pfwd_ldtype_i,
    input   logic [STBUFF_IDX_LEN:0]    vfwd_older_stores_i,
    input   logic [STBUFF_IDX_LEN:0]    pfwd_older_stores_i,
    output  logic [STBUFF_IDX_LEN:0]    inflight_store_cnt_o, // number of uncommitted store instructions in the store buffer
    output  logic                       lb_store_committing_o, // A store is committing in the store buffer
    output  logic                       vfwd_hit_o,
    output  logic                       vfwd_depfree_o,
    output  logic                       pfwd_hit_o,
    output  logic                       pfwd_depfree_o,
    output  logic [XLEN-1:0]            vfwd_value_o,
    output  logic [XLEN-1:0]            pfwd_value_o,

    // Control from/to the ROB
    input   logic [ROB_IDX_LEN-1:0]     rob_head_idx_i,
    output  logic                       rob_store_committing_o,

    // Hanshake from/to the CDB 
    input   logic                       cdb_ready_i,
    input   logic                       cdb_valid_i,        // to know if the CDB is carrying valid data
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

    // Store buffer pointers
    logic [STBUFF_IDX_LEN-1:0]      sb_head_idx, sb_tail_idx; // head and tail pointers
    logic [STBUFF_IDX_LEN-1:0]      vadder_req_idx, dtlb_req_idx, cdb_req_idx; // request indexes
    logic                           vadder_idx_valid, dtlb_idx_valid, cdb_idx_valid;

    // head and tail counters control
    logic                           head_cnt_en, head_cnt_clr, tail_cnt_en, tail_cnt_clr;

    // In-flight stores counter
    logic [STBUFF_IDX_LEN:0]        inflight_count; 

    // Operation control
    logic                           sb_push, sb_pop, sb_vadder_req, sb_vadder_ans, sb_dtlb_req, sb_dtlb_wu, sb_dtlb_ans, sb_dcache_req, sb_dcache_wu, sb_dcache_ans, sb_cdb_req, sb_store_committing;

    // Store buffer data structure
    sb_entry_t                      sb_data[0:STBUFF_DEPTH-1];

    // Status signals 
    logic [STBUFF_DEPTH-1:0]        valid_a, busy_a, rs1_ready_a, vaddr_ready_a, paddr_ready_a, except_raised_a, completed_a;
    `ifdef ENABLE_AGE_BASED_SELECTOR
    logic [ROB_IDX_LEN-1:0]         entry_age_a [0:STBUFF_DEPTH-1];
    `endif
    logic [XLEN-1:0]                paddr_a [0:STBUFF_DEPTH-1];

    //-------------------------------------\\
    //----- STATUS SIGNALS GENERATION -----\\
    //-------------------------------------\\
    // These are required because name selection after indexing is not supported
    always_comb begin: status_signals_gen
        for (int i = 0; i < STBUFF_DEPTH; i++) begin
            valid_a[i]          = sb_data[i].valid;
            busy_a[i]           = sb_data[i].busy;
            rs1_ready_a[i]      = sb_data[i].rs1_ready;
            //rs2_ready_a[i]      = sb_data[i].rs2_ready;   /* TODO: do we need this? */
            vaddr_ready_a[i]    = sb_data[i].vaddr_ready;
            paddr_ready_a[i]    = sb_data[i].paddr_ready;
            except_raised_a[i]  = sb_data[i].except_raised;
            completed_a[i]      = sb_data[i].completed;
            `ifdef ENABLE_AGE_BASED_SELECTOR
            entry_age_a[i]      = sb_data[i].entry_age;
            `endif
        end
    end

    //-------------------------------------\\
    //----- COMPLETE PHYSICAL ADDRESS -----\\
    //-------------------------------------\\
    always_comb begin: paddr_gen
        for (int i = 0; i < STBUFF_DEPTH; i++) begin
            paddr_a[i] = { {(XLEN-PADDR_LEN){1'b0}}, sb_data[i].ppn, sb_data[i].vaddr[PAGE_OFFSET_LEN-1:0] };
        end
    end

    //--------------------------------------\\
    //----- STORE BUFFER CONTROL LOGIC -----\\
    //--------------------------------------\\
    // Generates the control signals that trigger specific operations on the data structure based in input and status signals.
    always_comb begin: sb_control_logic
        // DEFAULT VALUES
        // Operation control
        sb_push             = 1'b0;
        sb_pop              = 1'b0;
        
        sb_vadder_req       = 1'b0;
        sb_vadder_ans       = 1'b0;
        
        sb_dtlb_req         = 1'b0;
        sb_dtlb_wu          = 1'b0;
        sb_dtlb_ans         = 1'b0;
        
        sb_dcache_req       = 1'b0;
        sb_dcache_wu        = 1'b0;
        sb_dcache_ans       = 1'b0;

        sb_store_committing = 1'b0;

        // Handshake control
        issue_logic_ready_o     = 1'b0;
        
        vadder_valid_o      = 1'b0;
        vadder_ready_o      = 1'b1;     // Always ready to accept computed virtual address
        
        dtlb_valid_o        = 1'b0;
        dtlb_ready_o        = 1'b1;     // Always ready to accept the physical address
        
        dcache_valid_o      = 1'b0;
        dcache_ready_o      = 1'b1;     // Always ready to accept D$ answer

        cdb_valid_o         = 1'b0;

        // Head and tail counters control
        head_cnt_en         = 1'b0;
        head_cnt_clr        = flush_i;  // clear when flushing 
        tail_cnt_en         = 1'b0;
        tail_cnt_clr        = flush_i;  // clear when flushing 

        //--------------------\\
        //----- REQUESTS -----\\
        //--------------------\\

        // PUSH NEW INSTRUCTION
        // Push a new instruction in the queue if the selected entry is empty (i.e. not valid) and the decoder is sending a valid instruction to the load buffer
        if (!sb_data[sb_tail_idx].valid/*&&!(stall)*/) begin
            issue_logic_ready_o = 1'b1; // Notify the arbiter that an instruction can be accepted
            if (issue_logic_valid_i) begin 
                sb_push = 1'b1; // If the arbiter is sending a valid instruction, push it into the queue
                tail_cnt_en = 1'b1;
            end
        end

        // REQUEST TO THE VIRTUAL ADDRESS ADDER
        // The selected entry must be valid (other checks are performed by the selector)
        if (sb_data[vadder_req_idx].valid/*&&!(stall)*/) begin
            vadder_valid_o = 1'b1;
            if (vadder_ready_i) sb_vadder_req = 1'b1; // The adder can accept the request, and the entry is marked as busy
        end

        // REQUEST TO THE TLB
        // The selected entry must be valid (other checks are performed by the selector)
        if (sb_data[dtlb_req_idx].valid/*&&!(stall)*/) begin
            dtlb_valid_o = 1'b1; // The TLB can accept the request, so the entry can be marked as busy
            if (dtlb_ready_i) sb_dtlb_req = 1'b1;
        end

        // REQUEST TO THE D$
        // The cache request can be performed if the head instruction of the store buffer:
        // - is also the head entry of the ROB (in-order execution of store instructions)
        // - is valid
        // - is not busy (it hasn't performed the request yet)
        // - has no recorded exceptions
        // - has its physical address ready
        // - is not completed
        if (rob_head_idx_i == sb_data[sb_head_idx].dest_idx/*&&!(stall)*/) begin
            if (sb_data[sb_head_idx].valid && !sb_data[sb_head_idx].busy && !sb_data[sb_head_idx].except_raised && sb_data[sb_head_idx].paddr_ready && !sb_data[sb_head_idx].completed) begin
                dcache_valid_o = 1'b1;
                if (dcache_ready_i) sb_dcache_req = 1'b1; // the D$ can accept the request
            end
        end

        // REQUEST TO THE CDB
        // The selected entry must be valid (other checks are performed by the selector)
        if (sb_data[cdb_req_idx].valid/*&&!(stall)*/) begin
            cdb_valid_o = 1'b1;
            if (cdb_ready_i) sb_cdb_req = 1'b1; // the CDB can accept the request, so the entry can be marked as completed
        end

        // POP INSTRUCTION
        // The head instruction can be popped if it's completed and its also at the head of the ROB. This corresponds to the instruction commit. 
        if (sb_data[sb_head_idx].valid && sb_data[sb_head_idx].completed && (rob_head_idx_i == sb_data[sb_head_idx].dest_idx)/*&&!(stall)*/) begin
            sb_pop = 1'b1;
            sb_store_committing = 1'b1; // Notify the ROB and the load buffer that a store is committing
            head_cnt_en = 1'b1;
        end

        //-------------------\\
        //----- ANSWERS -----\\
        //-------------------\\

        // VIRTUAL ADDRESS ADDER ANSWER
        if (vadder_valid_i) begin
            sb_vadder_ans = 1'b1;
        end 

        // TLB ANSWER/WAKE-UP
        if (dtlb_wu_valid_i) begin
            sb_dtlb_wu = 1'b1;
        end 
        if (dtlb_ans_valid_i) begin
            sb_dtlb_ans = 1'b1; 
        end

        // D$ ANSWER/WAKE-UP
        if (dcache_wu_valid_i) begin
            sb_dcache_wu = 1'b1;
        end
        if (dcache_ans_valid_i) begin
            sb_dcache_ans = 1'b1;
        end
    
    end

    //------------------------------------\\
    //----- STORE BUFFER DATA UPDATE -----\\
    //------------------------------------\\
    always_ff @(posedge clk_i or negedge rst_n_i) begin: sb_data_update
        if (!rst_n_i) begin // Asynchronous reset
            foreach (sb_data[i]) begin
                sb_data[i]                  <= 0;
            end
        end else if (flush_i) begin // Synchronous flush: clering status fields is enough
            foreach (sb_data[i]) begin
                sb_data[i].valid            <= 1'b0;
                sb_data[i].busy             <= 1'b0;
                sb_data[i].rs1_ready        <= 1'b0;
                sb_data[i].rs2_ready        <= 1'b0;
                sb_data[i].vaddr_ready      <= 1'b0;
                sb_data[i].paddr_ready      <= 1'b0;
                sb_data[i].except_raised    <= 1'b0;
                sb_data[i].completed        <= 1'b0;
            end
        end else begin 

            //-------------------------------\\
            //----- PARALLEL OPERATIONS -----\\
            //-------------------------------\\

            foreach (sb_data[i]) begin
                
                // RETRIEVE BASE ADDRES AND VALUE TO BE STORED FROM THE CDB (parallel port 1: rs1_value)
                if (sb_data[i].valid && !sb_data[i].rs1_ready) begin
                    if (cdb_valid_i && !cdb_except_raised_i && (sb_data[i].rs1_idx == cdb_idx_i)) begin
                        sb_data[i].rs1_ready <= 1'b1;
                        sb_data[i].rs1_value <= cdb_data_i;
                    end
                end
                if (sb_data[i].valid && !sb_data[i].rs2_ready) begin
                    if (cdb_valid_i && !cdb_except_raised_i && (sb_data[i].rs2_idx == cdb_idx_i)) begin
                        sb_data[i].rs2_ready <= 1'b1;
                        sb_data[i].rs2_value <= cdb_data_i;
                    end
                end

                // TLB WAKE UP
                if (sb_dtlb_wu) begin
                    if (sb_data[i].valid && sb_data[i].busy && !sb_data[i].paddr_ready && (sb_data[i].vaddr[VADDR_LEN-1:PAGE_OFFSET_LEN] == dtlb_vaddr_i)) begin
                        // Exception handling
                        case(dtlb_except_i)
                            PageFault: begin
                                sb_data[i].busy             <= 1'b0; 
                                sb_data[i].except_raised    <= 1'b1;
                                sb_data[i].except_code      <= E_ST_PAGE_FAULT;
                                sb_data[i].rs2_value        <= sb_data[i].vaddr; // copy the offending virtual address in the result field so it can be used during exception handling (this overwrites the valued to be copied in memory)
                                sb_data[i].completed        <= 1'b1; // mark the entry as completed so the cache access is skipped
                            end
                            AccessException: begin
                                sb_data[i].busy             <= 1'b0; 
                                sb_data[i].except_raised    <= 1'b1;
                                sb_data[i].except_code      <= E_ST_ACCESS_FAULT;
                                sb_data[i].rs2_value        <= sb_data[i].vaddr; // copy the offending virtual address in the result field so it can be used during exception handling
                                sb_data[i].completed        <= 1'b1; // mark the entry as completed so the cache access is skipped
                            end
                            NoException: begin // normal execution
                                sb_data[i].busy             <= 1'b0; // clear busy bit so the instruction can be replayed
                            end
                            default: begin
                                sb_data[i].busy             <= 1'b0; // clear busy so vaddr forwarding is skipped
                                sb_data[i].except_raised    <= 1'b1;
                                sb_data[i].except_code      <= E_UNKNOWN; // reserved code 10
                                sb_data[i].rs2_value        <= sb_data[i].vaddr;
                                sb_data[i].completed        <= 1'b1;
                            end
                        endcase
                    end
                end
            end

            //----------------------------\\
            //----- WRITE OPERATIONS -----\\
            //----------------------------\\

            // PUSH NEW INSTRUCTION
            if (sb_push) begin
                sb_data[sb_tail_idx].valid          <= 1'b1;
                sb_data[sb_tail_idx].busy           <= 1'b0;
                `ifdef ENABLE_AGE_BASED_SELECTOR
                sb_data[sb_tail_idx].entry_age      <= 0;
                `endif
                sb_data[sb_tail_idx].store_type     <= store_type_i;
                sb_data[sb_tail_idx].rs1_ready      <= rs1_ready_i;
                sb_data[sb_tail_idx].rs1_idx        <= rs1_idx_i;
                sb_data[sb_tail_idx].rs1_value      <= rs1_value_i;
                sb_data[sb_tail_idx].rs2_ready      <= rs2_ready_i;
                sb_data[sb_tail_idx].rs2_idx        <= rs2_idx_i;
                sb_data[sb_tail_idx].rs2_value      <= rs2_value_i;
                sb_data[sb_tail_idx].imm_value      <= imm_value_i;
                sb_data[sb_tail_idx].vaddr_ready    <= 1'b0;
                sb_data[sb_tail_idx].paddr_ready    <= 1'b0;
                sb_data[sb_tail_idx].dest_idx       <= dest_idx_i;
                sb_data[sb_tail_idx].except_raised  <= 1'b0;
                sb_data[sb_tail_idx].completed      <= 1'b0;

                `ifdef ENABLE_AGE_BASED_SELECTOR
                // Update the age of all valid entries
                foreach(sb_data[i]) begin
                    if (sb_tail_idx != i[STBUFF_IDX_LEN-1:0] && sb_data[i].valid) sb_data[i].entry_age <= sb_data[i].entry_age + 1;
                end
                `endif
            end

            // REQUEST TO THE VIRTUAL ADDRESS ADDER
            if (sb_vadder_req) begin
                sb_data[vadder_req_idx].busy    <= 1'b1;
            end

            // REQUEST TO THE TLB
            if (sb_dtlb_req) begin
                sb_data[dtlb_req_idx].busy      <= 1'b1;
            end

            // REQUEST TO THE D$
            if (sb_dcache_req) begin
                sb_data[sb_head_idx].busy       <= 1'b1;
            end

            // POP THE HEAD INSTRUCTION (COMMIT)
            if (sb_pop) begin
                sb_data[sb_head_idx].valid      <= 1'b0; // Pop the committed instruction
            end
            
            //--------------------------\\
            //----- PROCESS ANWERS -----\\
            //--------------------------\\

            // VIRTUAL ADDRESS ADDER ANSWER (WRITE PORT 1: entry.vaddr, entry.rs2_value)
            if (sb_vadder_ans) begin
                // Exception handling
                case(vadder_except_i)
                    VADDER_ALIGN_EXCEPT: begin
                        sb_data[vadder_idx_i].busy          <= 1'b0; 
                        sb_data[vadder_idx_i].except_raised <= 1'b1;
                        sb_data[vadder_idx_i].except_code   <= E_ST_ADDR_MISALIGNED;
                        sb_data[vadder_idx_i].rs2_value     <= vadder_vaddr_i; // The virtual address is copied in the rs2 value field instead of the loaded value, so it will be sent to the CDB (i.e. the ROB)
                        sb_data[vadder_idx_i].completed     <= 1'b1; // Mark the entry as completed so TLB and D$ accesses are skipped
                    end
                    VADDER_PAGE_EXCEPT: begin
                        sb_data[vadder_idx_i].busy          <= 1'b0; 
                        sb_data[vadder_idx_i].except_raised <= 1'b1;
                        sb_data[vadder_idx_i].except_code   <= E_ST_PAGE_FAULT;
                        sb_data[vadder_idx_i].rs2_value     <= vadder_vaddr_i; // The virtual address is copied in the rs2 value field so it will be sent to the CDB (i.e. the ROB)
                        sb_data[vadder_idx_i].completed     <= 1'b1; // Mark the entry as completed so TLB and D$ accesses are skipped
                    end
                    VADDER_NO_EXCEPT: begin
                        // If virtual memory is not enabled, save the virtual address in the physical address field
                        if (vm_mode_i == BARE) begin
                            sb_data[vadder_idx_i].paddr_ready <= 1'b1;
                            sb_data[vadder_idx_i].ppn       <= vadder_vaddr_i[PADDR_LEN-1:PAGE_OFFSET_LEN];
                        end
                        sb_data[vadder_idx_i].busy          <= 1'b0; // clear the busy bit so the entry can proceed to the TLB access
                        sb_data[vadder_idx_i].vaddr_ready   <= 1'b1; // the virtual address is available
                        sb_data[vadder_idx_i].vaddr         <= vadder_vaddr_i; // the virtual address is copied in the entry
                    end
                    default: begin // unknown exception
                        sb_data[vadder_idx_i].busy          <= 1'b0; 
                        sb_data[vadder_idx_i].except_raised <= 1'b1;
                        sb_data[vadder_idx_i].except_code   <= E_UNKNOWN; // reserved code d10
                        sb_data[vadder_idx_i].rs2_value     <= vadder_vaddr_i;
                        sb_data[vadder_idx_i].completed     <= 1'b1;
                    end
                endcase
            end

            // TLB ANSWER (WRITE PORT 2: entry.ppn, entry.rs2_value)
            if (sb_dtlb_ans) begin
                // Exception handling
                case(dtlb_except_i)
                    PageFault: begin
                        sb_data[dtlb_idx_i].busy            <= 1'b0; 
                        sb_data[dtlb_idx_i].except_raised   <= 1'b1;
                        sb_data[dtlb_idx_i].except_code     <= E_ST_PAGE_FAULT;
                        sb_data[dtlb_idx_i].rs2_value       <= sb_data[dtlb_idx_i].vaddr; // copy the offending virtual address in the rs2 value field so it can be used during exception handling
                        sb_data[dtlb_idx_i].completed       <= 1'b1; // mark the entry as completed so the cache access is skipped
                    end
                    AccessException: begin
                        sb_data[dtlb_idx_i].busy            <= 1'b0; 
                        sb_data[dtlb_idx_i].except_raised   <= 1'b1;
                        sb_data[dtlb_idx_i].except_code     <= E_ST_ACCESS_FAULT;
                        sb_data[dtlb_idx_i].rs2_value       <= sb_data[dtlb_idx_i].vaddr; // copy the offending virtual address in the rs2 value field so it can be used during exception handling
                        sb_data[dtlb_idx_i].completed       <= 1'b1; // mark the entry as completed so the cache access is skipped
                    end
                    NoException: begin // normal execution
                        sb_data[dtlb_idx_i].busy            <= 1'b0; // clear busy bit so the entry can proceed to cache access
                        sb_data[dtlb_idx_i].paddr_ready     <= 1'b1;
                        sb_data[dtlb_idx_i].ppn             <= dtlb_ppn_i; // last 12 bits are not translated
                    end
                    default: begin
                        sb_data[dtlb_idx_i].busy            <= 1'b0;
                        sb_data[dtlb_idx_i].except_raised   <= 1'b1;
                        sb_data[dtlb_idx_i].except_code     <= E_UNKNOWN; // reserved code 10
                        sb_data[dtlb_idx_i].rs2_value       <= sb_data[dtlb_idx_i].vaddr;
                        sb_data[dtlb_idx_i].completed       <= 1'b1;
                    end
                endcase
            end

            // D$ ANSWER (WRITE PORT 3: entry.value)
            if (sb_dcache_ans) begin
                sb_data[dcache_idx_i].busy      <= 1'b0; // clear the busy bit
                sb_data[dcache_idx_i].completed <= 1'b1; // mark instruction as completed so it can commit
            end

            // D$ WAKE-UP: only the head entry can be waken up being the only one that performed the cache request
            if (sb_dcache_wu) begin
                if (sb_data[sb_head_idx].valid && sb_data[sb_head_idx].busy && sb_data[sb_head_idx].paddr_ready && (paddr_a[sb_head_idx][XLEN-1:(DCACHE_L1_WORD_A_LEN+DCACHE_L1_LINE_OFF_A_LEN)] == dcache_lineaddr_i)) begin
                    sb_data[sb_head_idx].busy <= 1'b0; // clear the busy bit so the instruction can be replayed
                end
            end

            // CDB ANSWER
            if (sb_cdb_req) begin
                sb_data[cdb_req_idx].completed <= 1'b1; // the entry is marked as completed so it will skip TLB access, D$ access and won't be selected again to write on the CDB
            end
        end
    end

    //----------------------------\\
    //----- FORWARDING LOGIC -----\\
    //----------------------------\\

    // VIRTUAL ADDRESS FORWARDING (PARALLEL ACCES 1: very complex due to RAW hazard check)
    logic vfwd_allowed, vfwd_hit, vfwd_depfree;
    logic [STBUFF_IDX_LEN-1:0] vfwd_idx;

    always_comb begin: virtual_fwd_logic
        
        // Default values:
        vfwd_allowed    = 1'b1;
        vfwd_depfree    = 1'b1;
        vfwd_idx        = 0;

        for (int i = 0; i < STBUFF_DEPTH; i++) begin
            if ((i[STBUFF_IDX_LEN-1:0] - sb_tail_idx) < (sb_head_idx + vfwd_older_stores_i - sb_tail_idx)) begin
                if (!sb_data[i].vaddr_ready) vfwd_allowed = 1'b0;
                else if ((i[STBUFF_IDX_LEN-1:0] - sb_tail_idx) >= vfwd_idx - sb_tail_idx) begin
                    case(sb_data[i].store_type)

                        LS_DOUBLEWORD: begin
                            if (vfwd_vaddr_i[XLEN-1 : 3] == sb_data[i].vaddr[XLEN-1 : 3]) begin
                                vfwd_depfree    = 1'b0;
                                vfwd_idx        = i[STBUFF_IDX_LEN-1:0];
                            end
                        end

                        LS_WORD, LS_WORD_U: begin
                            case(vfwd_ldtype_i)
                                LS_DOUBLEWORD: begin
                                    vfwd_allowed = 1'b0; // can't load a doubleword from a word
                                    vfwd_depfree = 1'b0;
                                end
                                LS_WORD, LS_WORD_U, LS_HALFWORD, LS_HALFWORD_U, LS_BYTE, LS_BYTE_U: begin
                                   if (vfwd_vaddr_i[XLEN-1 : 2] == sb_data[i].vaddr[XLEN-1 : 2]) begin
                                        vfwd_depfree    = 1'b0;
                                        vfwd_idx        = i[STBUFF_IDX_LEN-1:0];
                                    end else begin
                                        vfwd_allowed = 1'b0; // can't load the other word
                                        vfwd_depfree = 1'b0;
                                    end
                                end
                                default: vfwd_allowed = 1'b0;
                            endcase
                        end

                        LS_HALFWORD, LS_HALFWORD_U: begin
                            case(vfwd_ldtype_i)
                                LS_DOUBLEWORD, LS_WORD, LS_WORD_U: begin
                                    vfwd_allowed = 1'b0; // can't load a doubleword or a word from a halfword
                                    vfwd_depfree = 1'b0;
                                end
                                LS_HALFWORD, LS_HALFWORD_U, LS_BYTE, LS_BYTE_U: begin
                                   if (vfwd_vaddr_i[XLEN-1 : 1] == sb_data[i].vaddr[XLEN-1 : 1]) begin
                                        vfwd_depfree    = 1'b0;
                                        vfwd_idx        = i[STBUFF_IDX_LEN-1:0];
                                    end else begin
                                        vfwd_allowed = 1'b0; // can't load the other halfwords
                                        vfwd_depfree = 1'b0;
                                    end
                                end
                                default: vfwd_allowed = 1'b0;
                            endcase
                        end

                        LS_BYTE, LS_BYTE_U: begin
                            case(vfwd_ldtype_i)
                                LS_DOUBLEWORD, LS_WORD, LS_WORD_U, LS_HALFWORD, LS_HALFWORD_U: begin
                                    vfwd_allowed = 1'b0; // can't load a doubleword, word or halfword from a byte
                                    vfwd_depfree = 1'b0;
                                end
                                LS_BYTE, LS_BYTE_U: begin
                                   if (vfwd_vaddr_i == sb_data[i].vaddr) begin
                                        vfwd_depfree    = 1'b0;
                                        vfwd_idx        = i[STBUFF_IDX_LEN-1:0];
                                    end else begin
                                        vfwd_allowed = 1'b0; // can't load the other bytes
                                        vfwd_depfree = 1'b0;
                                    end
                                end
                                default: vfwd_allowed = 1'b0;
                            endcase
                        end

                        default: vfwd_allowed = 1'b0;
                    endcase
                end
            end
        end

        // Hit only if the most recent older store have the data available
        vfwd_hit = (sb_data[vfwd_idx].rs2_ready) ? 1'b1 : 1'b0;
    end

    // PHYSICAL ADDRESS FORWARDING (PARALLEL ACCES 2: very complex due to RAW hazard check)
    logic pfwd_allowed, pfwd_hit, pfwd_depfree;
    logic [STBUFF_IDX_LEN-1:0] pfwd_idx;

    always_comb begin: physical_fwd_logic
        
        // Default values:
        pfwd_allowed    = 1'b1;
        pfwd_depfree    = 1'b1;
        pfwd_idx        = 0;

        for (int i = 0; i < STBUFF_DEPTH; i++) begin
            if ((i[STBUFF_IDX_LEN-1:0] - sb_tail_idx) < (sb_head_idx + pfwd_older_stores_i - sb_tail_idx)) begin
                if (!sb_data[i].paddr_ready) pfwd_allowed = 1'b0;
                else if ((i[STBUFF_IDX_LEN-1:0] - sb_tail_idx) >= pfwd_idx - sb_tail_idx) begin
                    case(sb_data[i].store_type)

                        LS_DOUBLEWORD: begin
                            if (pfwd_paddr_i[XLEN-1 : 3] == paddr_a[i][XLEN-1 : 3]) begin
                                pfwd_depfree    = 1'b0;
                                pfwd_idx        = i[STBUFF_IDX_LEN-1:0];
                            end
                        end

                        LS_WORD, LS_WORD_U: begin
                            case(pfwd_ldtype_i)
                                LS_DOUBLEWORD: begin
                                    pfwd_allowed = 1'b0; // can't load a doubleword from a word
                                    pfwd_depfree = 1'b0;
                                end
                                LS_WORD, LS_WORD_U, LS_HALFWORD, LS_HALFWORD_U, LS_BYTE, LS_BYTE_U: begin
                                   if (pfwd_paddr_i[XLEN-1 : 2] == paddr_a[i][XLEN-1 : 2]) begin
                                        pfwd_depfree    = 1'b0;
                                        pfwd_idx        = i[STBUFF_IDX_LEN-1:0];
                                    end else begin
                                        pfwd_allowed = 1'b0; // can't load the other word
                                        pfwd_depfree = 1'b0;
                                    end
                                end
                                default: pfwd_allowed = 1'b0;
                            endcase
                        end

                        LS_HALFWORD, LS_HALFWORD_U: begin
                            case(pfwd_ldtype_i)
                                LS_DOUBLEWORD, LS_WORD, LS_WORD_U: begin
                                    pfwd_allowed = 1'b0; // can't load a doubleword or a word from a halfword
                                    pfwd_depfree = 1'b0;
                                end
                                LS_HALFWORD, LS_HALFWORD_U, LS_BYTE, LS_BYTE_U: begin
                                   if (pfwd_paddr_i[XLEN-1 : 1] == paddr_a[i][XLEN-1 : 1]) begin
                                        pfwd_depfree    = 1'b0;
                                        pfwd_idx        = i[STBUFF_IDX_LEN-1:0];
                                    end else begin
                                        pfwd_allowed = 1'b0; // can't load the other halfwords
                                        pfwd_depfree = 1'b0;
                                    end
                                end
                                default: pfwd_allowed = 1'b0;
                            endcase
                        end

                        LS_BYTE, LS_BYTE_U: begin
                            case(pfwd_ldtype_i)
                                LS_DOUBLEWORD, LS_WORD, LS_WORD_U, LS_HALFWORD, LS_HALFWORD_U: begin
                                    pfwd_allowed = 1'b0; // can't load a doubleword, word or halfword from a byte
                                    pfwd_depfree = 1'b0;
                                end
                                LS_BYTE, LS_BYTE_U: begin
                                   if (pfwd_paddr_i == paddr_a[i]) begin
                                        pfwd_depfree    = 1'b0;
                                        pfwd_idx        = i[STBUFF_IDX_LEN-1:0];
                                    end else begin
                                        pfwd_allowed = 1'b0; // can't load the other bytes
                                        pfwd_depfree = 1'b0;
                                    end
                                end
                                default: pfwd_allowed = 1'b0;
                            endcase
                        end

                        default: pfwd_allowed = 1'b0;
                    endcase
                end
            end
        end

        // Hit only if the most recent older store have the data available
        pfwd_hit = (sb_data[pfwd_idx].rs2_ready) ? 1'b1 : 1'b0;
    end


    //------------------------------------\\
    //----- IN-FLIGHT STORES COUNTER -----\\
    //------------------------------------\\
    // It is the difference between the tail and head pointers. However, when the store buffer is full of uncommitted stores, this difference is 0, like when the buffer is empty. So, the MSB is set accordingly.
    assign inflight_count[STBUFF_IDX_LEN]       = &valid_a; // MSB is 1 if all are valid
    assign inflight_count[STBUFF_IDX_LEN-1:0]   = sb_tail_idx - sb_head_idx;
    
    //----------------------------------\\
    //----- HEAD AND TAIL COUNTERS -----\\
    //----------------------------------\\
    modn_counter #(.N(STBUFF_DEPTH)) head_counter
    (
        .clk_i      (clk_i),
        .rst_n_i    (rst_n_i),
        .en_i       (head_cnt_en),
        .clr_i      (head_cnt_clr),
        .count_o    (sb_head_idx),
        .tc_o       ()              // Not needed
    );

    modn_counter #(.N(STBUFF_DEPTH)) tail_counter
    (
        .clk_i      (clk_i),
        .rst_n_i    (rst_n_i),
        .en_i       (tail_cnt_en),
        .clr_i      (tail_cnt_clr),
        .count_o    (sb_tail_idx),
        .tc_o       ()              // Not needed
    );
    
    //------------------------------------------------\\
    //----- VIRTUAL ADDRESS COMPUTATION SELECTOR -----\\
    //------------------------------------------------\\
    `ifdef ENABLE_AGE_BASED_SELECTOR
    // The selector follows a "first come first served" scheduling policy. The oldest valid entry whose base address from rs1 is available and whose virtual address hasn't been computed yet (vaddr_ready = 0) is selected to be sent to the virtual address adder
    age_based_sel #(.N(STBUFF_DEPTH), .AGE_LEN(ROB_IDX_LEN)) vaddr_req_selector
    (
        .lines_i    (valid_a & ~busy_a & rs1_ready_a & ~vaddr_ready_a & ~completed_a),
        .ages_i     (entry_age_a),
        .enc_o      (vadder_req_idx),
        .valid_o    (vadder_idx_valid)
    );
    `else
    // Simple priority encoder
    prio_enc #(.N(STBUFF_DEPTH)) vaddr_req_selector
    (
        .lines_i    (valid_a & ~busy_a & rs1_ready_a & ~vaddr_ready_a & ~completed_a),
        .enc_o      (vadder_req_idx),
        .valid_o    (vadder_idx_valid)
    );
    `endif

    //--------------------------------\\
    //----- DTLB ACCESS SELECTOR -----\\
    //--------------------------------\\
    `ifdef ENABLE_AGE_BASED_SELECTOR
    // The selector follows a "first come first served" scheduling policy. The oldest valid entry whose virtual address has already be computed and that's not busy or completed is selected for the address translation
    age_based_sel #(.N(STBUFF_DEPTH), .AGE_LEN(ROB_IDX_LEN)) dtlb_req_selector
    (
        .lines_i    (valid_a & ~busy_a & vaddr_ready_a & ~paddr_ready_a & ~except_raised_a & ~completed_a),
        .ages_i     (entry_age_a),
        .enc_o      (dtlb_req_idx),
        .valid_o    (dtlb_idx_valid)
    );
    `else
    // Simple priority encoder
    prio_enc #(.N(STBUFF_DEPTH)) dtlb_req_selector
    (
        .lines_i    (valid_a & ~busy_a & vaddr_ready_a & ~paddr_ready_a & ~except_raised_a & ~completed_a),
        .enc_o      (dtlb_req_idx),
        .valid_o    (dtlb_idx_valid)
    );
    `endif

    //------------------------\\
    //----- CDB SELECTOR -----\\
    //------------------------\\
    `ifdef ENABLE_AGE_BASED_SELECTOR
    // Stores access the CDB only to signal occurred exceptions to the ROB. Exceptions can be raised during the address translation or during the TLB access. 
    age_based_sel #(.N(STBUFF_DEPTH), .AGE_LEN(ROB_IDX_LEN)) cdb_req_selector
    (
        .lines_i    (valid_a & completed_a),
        .ages_i     (entry_age_a),
        .enc_o      (cdb_req_idx),
        .valid_o    (cdb_idx_valid)
    );
    `else
    // Simple priority encoder
    prio_enc #(.N(STBUFF_DEPTH)) cdb_req_selector
    (
        .lines_i    (valid_a & completed_a),
        .enc_o      (cdb_req_idx),
        .valid_o    (cdb_idx_valid)
    );
    `endif
    
    //-----------------------------\\
    //----- OUTPUT EVALUATION -----\\
    //-----------------------------\\

    // TO THE VIRTUAL ADDRESS ADDER (OPERANDS READ PORT 1)
    assign vadder_isstore_o = 1'b1;                                 // the instruction is a store
    assign rs1_value_o      = sb_data[vadder_req_idx].rs1_value;
    assign imm_value_o      = sb_data[vadder_req_idx].imm_value;
    assign vadder_idx_o     = vadder_req_idx;
    assign vadder_sttype_o  = sb_data[vadder_req_idx].store_type;

    // TO THE TLB
    assign dtlb_isstore_o = 1'b1; // the instruction is a store
    assign dtlb_vaddr_o = sb_data[dtlb_req_idx].vaddr[VADDR_LEN-1:PAGE_OFFSET_LEN]; // (VADDR READ PORT 1)
    assign dtlb_idx_o   = dtlb_req_idx;

    // TO THE D$ 
    assign dcache_isstore_o = 1'b1; // the instruction is a store
    assign dcache_paddr_o   = paddr_a[sb_head_idx];             // (PADDR READ PORT 1)
    assign dcache_value_o   = sb_data[sb_head_idx].rs2_value;   // (RS2 READ PORT 1)
    assign dcache_idx_o     = sb_head_idx;
    assign dcache_sttype_o  = sb_data[sb_head_idx].store_type;

    // TO THE LOAD BUFFER
    assign inflight_store_cnt_o     = inflight_count;
    assign lb_store_committing_o    = sb_store_committing;

    // VIRTUAL ADDRESS FORWARDING (PARALLEL PORT 1)
    // Virtual address forwarding is valid only if all previous stores have ready vaddr
    assign vfwd_depfree_o   = vfwd_allowed & vfwd_depfree;
    assign vfwd_hit_o       = vfwd_allowed & vfwd_hit;
    assign vfwd_value_o     = sb_data[vfwd_idx].rs2_value;      // (RS2 READ PORT 2)

    // VIRTUAL ADDRESS FORWARDING (PARALLEL PORT 2)
    // Phisical address forwarding is valid only if all previous stores have ready vaddr
    assign pfwd_depfree_o   = pfwd_allowed & pfwd_depfree;
    assign pfwd_hit_o       = pfwd_allowed & pfwd_hit;
    assign pfwd_value_o     = sb_data[pfwd_idx].rs2_value;      // (RS2 READ PORT 3)

    // TO THE ROB
    assign rob_store_committing_o = sb_store_committing;

    // TO THE CDB
    assign cdb_idx_o            = sb_data[cdb_req_idx].dest_idx;
    assign cdb_data_o           = sb_data[cdb_req_idx].rs2_value;   // (RS2 READ PORT 4)
    assign cdb_except_raised_o  = sb_data[cdb_req_idx].except_raised;
    assign cdb_except_o         = { {(ROB_EXCEPT_LEN-EXCEPT_TYPE_LEN){1'b0} }, sb_data[cdb_req_idx].except_code };
    
    //----------------------\\
    //----- ASSERTIONS -----\\
    //----------------------\\
    `ifndef SYNTHESIS
    always @(negedge clk_i) begin
        // Notice when the load buffer is full
        assert (valid_a !== '1) else $warning("Store buffer full: you might want to increase its depth");
        foreach (sb_data[i]) begin
            // Check if the correct order of operations is respected
            assert (sb_data[i].except_code != E_UNKNOWN) else $warning("Store buffer entry %4d has encountered an unknown exception", i);
        end
    end
    `endif

endmodule
