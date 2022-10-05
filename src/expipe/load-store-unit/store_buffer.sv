// Copyright 2022 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: store_buffer.sv
// Author: Michele Caon
// Date: 15/07/2022

// LEN5 compilation switches
`include "len5_config.svh"

// Import UVM report macros
`ifndef SYNTHESIS
`include "uvm_macros.svh"
import uvm_pkg::*;
`endif

import len5_pkg::XLEN;
import len5_pkg::except_code_t;
import len5_pkg::STBUFF_TAG_W;
import expipe_pkg::*;
import memory_pkg::*;

/**
 * @brief	Bare-metal store buffer.
 *
 * @details	Store buffer without support for virtual memory (no TLB), intended
 *          to be directly connected to a memory module.
 */
module store_buffer #(
    parameter DEPTH = 4
) (
    input   logic                       clk_i,
    input   logic                       rst_n_i,
    input   logic                       flush_i,

    /* Issue stage */
    input   logic                       issue_valid_i,
    output  logic                       issue_ready_o,
    input   ldst_width_t                issue_type_i,       // byte, halfword, ...
    input   op_data_t                   issue_rs1_i,        // base address
    input   op_data_t                   issue_rs2_i,        // data to store
    input   logic [XLEN-1:0]            issue_imm_i,        // offset
    input   rob_idx_t                   issue_dest_rob_idx_i,

    /* Commit stage */
    input   logic                       comm_spec_instr_i, // there are older jump/branch in-fligh instructions
    input   rob_idx_t                   comm_rob_head_idx_i,

    /* Common data bus (CDB) */
    input   logic                       cdb_valid_i,
    input   logic                       cdb_ready_i,
    output  logic                       cdb_valid_o,
    input   cdb_data_t                  cdb_data_i,
    output  cdb_data_t                  cdb_data_o,

    /* Address adder */
    input   logic                       adder_valid_i,
    input   logic                       adder_ready_i,
    output  logic                       adder_valid_o,
    output  logic                       adder_ready_o,
    input   adder_ans_t                 adder_ans_i,
    output  adder_req_t                 adder_req_o,

    /* Load buffer (for load-after-store dependencies) */
    output  logic                       lb_latest_valid_o,      // the latest store tag is valid
    output  logic [STBUFF_TAG_W-1:0]    lb_latest_tag_o,        // tag of the latest store
    output  logic                       lb_oldest_completed_o,  // the oldest store has completed 
    output  logic [STBUFF_TAG_W-1:0]    lb_oldest_tag_o,        // tag of the oldest active store

    /* Memory system */
    input   logic                       mem_valid_i,
    input   logic                       mem_ready_i,
    output  logic                       mem_valid_o,
    output  logic                       mem_ready_o,
    output  mem_req_t                   mem_req_o,
    input   mem_ans_t                   mem_ans_i

    /* Load buffer (store-to-load forwarding) */ /* TODO */
    // input   logic [XLEN-1:0]            lb_addr_i,          // load address
    // input   ldst_width_t                 lb_type_i,          // load type
    // input   logic [STBUFF_TAG_W:0]    lb_older_cnt_i,     // nummber of older store instructions
    // output  logic [STBUFF_TAG_W-1:0]  lb_pending_cnt_o,   // number of uncommitted store instructions
    // output  logic                       lb_committing_o,    // a store is committing
    // output  logic                       lb_hit_o,           // store data can be forwarded
    // output  logic [XLEN-1:0]            lb_value_o,         // store value
);

    // INTERNAL SIGNALS
    // ----------------

    // Head, tail, and address calculation counters
    logic [$clog2(DEPTH)-1:0]   head_idx, tail_idx, addr_idx, mem_idx;
    logic                       head_cnt_en, tail_cnt_en, addr_cnt_en, mem_cnt_en;
    logic                       head_cnt_clr, tail_cnt_clr, addr_cnt_clr, mem_cnt_clr;

    // Generic status signals
    logic           empty;  // the load buffer is empty

    // Latest store tag
    logic [$clog2(DEPTH)-1:0]   latest_tag;

    // Load buffer data
    sb_data_t       data[DEPTH];
    sb_state_t      curr_state[DEPTH], next_state[DEPTH];

    // Load buffer control
    logic           push, pop, save_rs, addr_accepted, save_addr, mem_accepted, mem_done;
    logic           spec_store_exec;
    logic           match_rs1[DEPTH], match_rs2[DEPTH];
    sb_op_t         sb_op[DEPTH];

    // -----------------
    // FIFO CONTROL UNIT
    // -----------------

    // Push, pop, save controls
    assign  push            = issue_valid_i & issue_ready_o;
    assign  pop             = cdb_valid_o & cdb_ready_i;
    assign  save_rs         = cdb_valid_i;
    assign  addr_accepted   = adder_valid_o & adder_ready_i;
    assign  save_addr       = adder_valid_i & adder_ready_o;
    assign  mem_accepted    = mem_valid_o & mem_ready_i;
    assign  mem_done        = mem_valid_i & mem_ready_o;
  
    // Counters control
    assign  head_cnt_clr    = flush_i;
    assign  tail_cnt_clr    = flush_i;
    assign  addr_cnt_clr    = flush_i;
    assign  mem_cnt_clr     = flush_i;
    assign  head_cnt_en     = pop;
    assign  tail_cnt_en     = push;
    assign  addr_cnt_en     = addr_accepted;
    assign  mem_cnt_en      = mem_accepted;

    // Generic status signals
    always_comb begin : empty_gen
        empty   = 1'b0;
        foreach (curr_state[i]) empty |= curr_state[i] != STORE_S_EMPTY;
    end

    // Speculative store execution
    // NOTE: a speculative store instruction can be executed only when it
    // reaches the head of the ROB.
    assign  spec_store_exec = data[head_idx].dest_rob_idx == comm_rob_head_idx_i;

    // Matching operands tags
    always_comb begin : p_match_rs
        foreach (data[i]) begin
            match_rs1[i]    = (cdb_data_i.rob_idx == data[i].rs1_rob_idx);
            match_rs2[i]    = (cdb_data_i.rob_idx == data[i].rs2_rob_idx);
        end
    end

    // State progression
    // NOTE: Mealy to avoid sampling useless data
    always_comb begin : p_state_prog
        // Default operation
        foreach (sb_op[i])  sb_op[i] = STORE_OP_NONE;

        foreach (curr_state[i]) begin
            case (curr_state[i])
                STORE_S_EMPTY: begin // push
                    if (push && tail_idx == i) begin
                        sb_op[i]        = STORE_OP_PUSH;
                        if (issue_rs1_i.ready && issue_rs2_i.ready)
                            next_state[i]   = STORE_S_ADDR_REQ;
                        else if (!issue_rs1_i.ready && issue_rs2_i.ready)
                            next_state[i]   = STORE_S_RS1_PENDING;
                        else if (issue_rs1_i.ready && !issue_rs2_i.ready)
                            next_state[i]   = STORE_S_RS2_PENDING;
                        else
                            next_state[i]   = STORE_S_RS12_PENDING;
                    end else 
                        next_state[i] = STORE_S_EMPTY; 
                end
                STORE_S_RS12_PENDING: begin // save rs1 and/or rs2 value from CDB
                    if (save_rs) begin
                        if (match_rs1[i] && match_rs2[i]) begin
                            sb_op[i]        = STORE_OP_SAVE_RS12;
                            next_state[i]   = STORE_S_ADDR_REQ;
                        end else if (match_rs1[i]) begin
                            sb_op[i]        = STORE_OP_SAVE_RS1;
                            next_state[i]   = STORE_S_RS2_PENDING;
                        end else if (match_rs2[i]) begin
                            sb_op[i]        = STORE_OP_SAVE_RS2;
                            next_state[i]   = STORE_S_RS1_PENDING;
                        end else 
                            next_state[i]   = STORE_S_RS12_PENDING;
                    end else 
                        next_state[i]   = STORE_S_RS12_PENDING;
                end
                STORE_S_RS1_PENDING: begin // save rs2 value from CDB
                    if (save_rs && match_rs1[i]) begin
                        sb_op[i]        = STORE_OP_SAVE_RS1;
                        next_state[i]   = STORE_S_ADDR_REQ;
                    end else
                        next_state[i]   = STORE_S_RS1_PENDING;
                end
                STORE_S_RS2_PENDING: begin // save rs2 value from CDB
                    if (save_rs && match_rs2[i]) begin
                        sb_op[i]        = STORE_OP_SAVE_RS2;
                        next_state[i]   = STORE_S_ADDR_REQ;
                    end else
                        next_state[i]   = STORE_S_RS2_PENDING;
                end
                STORE_S_ADDR_REQ: begin // save address (from adder)
                    if (save_addr && adder_ans_i.tag == i) begin
                        sb_op[i]        = STORE_OP_SAVE_ADDR;
                        if (adder_ans_i.except_raised)
                            next_state[i]   = STORE_S_COMPLETED;
                        else if (data[i].speculative)
                            next_state[i]   = STORE_S_WAIT_ROB;
                        else
                            next_state[i]   = STORE_S_MEM_REQ;
                    end else if (addr_idx == i && addr_accepted)
                        next_state[i]   = STORE_S_ADDR_WAIT;
                    else
                        next_state[i]   = STORE_S_ADDR_REQ;
                end
                STORE_S_ADDR_WAIT: begin
                    if (save_addr && adder_ans_i.tag == i) begin
                        sb_op[i]        = STORE_OP_SAVE_ADDR;
                        if (adder_ans_i.except_raised)
                            next_state[i]   = STORE_S_COMPLETED;
                        else if (data[i].speculative)
                            next_state[i]   = STORE_S_WAIT_ROB;
                        else
                            next_state[i]   = STORE_S_MEM_REQ;
                    end else
                        next_state[i]   = STORE_S_ADDR_WAIT;
                end
                STORE_S_WAIT_ROB: begin
                    if (spec_store_exec) begin
                        next_state[i]   = STORE_S_MEM_REQ;
                    end else
                        next_state[i]   = STORE_S_WAIT_ROB;
                end
                STORE_S_MEM_REQ: begin // wait for commit
                    if (mem_ans_i.tag == i && mem_done) begin
                        sb_op[i]        = STORE_OP_SAVE_MEM;
                        next_state[i]   = STORE_S_COMPLETED;
                    end else if (mem_idx == i && mem_accepted) begin
                        next_state[i]   = STORE_S_MEM_WAIT;
                    end else
                        next_state[i]   = STORE_S_MEM_REQ;
                end
                STORE_S_MEM_WAIT: begin
                    if (mem_ans_i.tag == i && mem_done) begin
                        sb_op[i]        = STORE_OP_SAVE_MEM;
                        next_state[i]   = STORE_S_COMPLETED;
                    end else
                        next_state[i]   = STORE_S_MEM_WAIT;
                end
                STORE_S_COMPLETED: begin
                    if (pop && head_idx == i)
                        next_state[i]   = STORE_S_EMPTY;
                    else 
                        next_state[i]   = STORE_S_COMPLETED;
                end
                default: next_state[i]  = STORE_S_HALT;
            endcase
        end
    end

    // State update
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : p_state_update
        if (!rst_n_i) foreach (curr_state[i]) curr_state[i] <= STORE_S_EMPTY;
        else if (flush_i) foreach (curr_state[i]) curr_state[i] <= STORE_S_EMPTY;
        else curr_state <= next_state;
    end

    // ------------------
    // LOAD BUFFER UPDATE
    // ------------------

    // NOTE: operations priority:
    // 1) push
    // 2) pop
    // 3) update memory value
    // 4) update address
    // 5) update rs1 (from CDB)
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : p_lb_update
        if (!rst_n_i) begin
            foreach (data[i]) begin
                data[i]         <= '0;
            end
        end else begin
            /* Performed the required action for each instruction */
            foreach (sb_op[i]) begin
                case (sb_op[i])
                    STORE_OP_PUSH: begin
                        data[i].store_type      <= issue_type_i;
                        data[i].speculative     <= comm_spec_instr_i;
                        data[i].rs1_rob_idx     <= issue_rs1_i.rob_idx;
                        data[i].rs1_value       <= issue_rs1_i.value;
                        data[i].rs2_rob_idx     <= issue_rs2_i.rob_idx;
                        data[i].rs2_value       <= issue_rs2_i.value;
                        data[i].dest_rob_idx    <= issue_dest_rob_idx_i;
                        data[i].imm_addr_value  <= issue_imm_i;
                        data[i].except_raised   <= 1'b0;
                    end
                    STORE_OP_SAVE_RS12: begin
                        data[i].rs1_value       <= cdb_data_i.res_value;
                        data[i].rs2_value       <= cdb_data_i.res_value;
                    end
                    STORE_OP_SAVE_RS1: begin
                        data[i].rs1_value       <= cdb_data_i.res_value;
                    end
                    STORE_OP_SAVE_RS2: begin
                        data[i].rs2_value       <= cdb_data_i.res_value;
                    end
                    STORE_OP_SAVE_ADDR: begin
                        data[i].imm_addr_value  <= adder_ans_i.result;
                        data[i].except_raised   <= adder_ans_i.except_raised;
                        data[i].except_code     <= adder_ans_i.except_code;
                    end
                    STORE_OP_SAVE_MEM: begin
                        data[i].except_raised   <= mem_ans_i.except_raised;
                        data[i].except_code     <= mem_ans_i.except_code;
                    end
                    default:;
                endcase
            end
        end
    end

    // Latest store instruction tag update
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : latest_tag_reg
        if (!rst_n_i)       latest_tag  <= '0;
        else if (flush_i)   latest_tag  <= '0;
        else if (push)      latest_tag  <= tail_idx;
    end

    // -----------------
    // OUTPUT EVALUATION
    // -----------------

    /* Issue stage */
    assign  issue_ready_o  = curr_state[tail_idx] == STORE_S_EMPTY;
    
    /* CDB */
    // NOTE: save memory address in result field for exception handling (mtval)
    assign  cdb_valid_o              = curr_state[head_idx] == STORE_S_COMPLETED;
    assign  cdb_data_o.rob_idx       = data[head_idx].dest_rob_idx;
    assign  cdb_data_o.res_value     = data[head_idx].imm_addr_value;
    assign  cdb_data_o.res_aux       = data[head_idx].rs2_value;
    assign  cdb_data_o.except_raised = data[head_idx].except_raised;
    assign  cdb_data_o.except_code   = data[head_idx].except_code;

    /* Address adder */
    assign  adder_valid_o          = curr_state[addr_idx] == STORE_S_ADDR_REQ;
    assign  adder_ready_o          = 1'b1; // always ready to accept data from the adder
    assign  adder_req_o.tag        = addr_idx;
    assign  adder_req_o.is_store   = 1'b1;
    assign  adder_req_o.base       = data[addr_idx].rs1_value;
    assign  adder_req_o.offs       = data[addr_idx].imm_addr_value;
    assign  adder_req_o.ls_type    = data[addr_idx].store_type;

    /* Load buffer */
    assign  lb_latest_valid_o       = !empty;
    assign  lb_latest_tag_o         = latest_tag;
    assign  lb_oldest_completed_o   = mem_done;
    assign  lb_oldest_tag_o         = mem_ans_i.tag;

    /* Memory system */
    assign  mem_valid_o         = curr_state[mem_idx] == STORE_S_MEM_REQ;
    assign  mem_ready_o         = 1'b1;
    assign  mem_req_o.tag       = mem_idx;
    assign  mem_req_o.acc_type  = MEM_ACC_ST;
    assign  mem_req_o.ls_type   = data[mem_idx].store_type;
    assign  mem_req_o.addr      = data[mem_idx].imm_addr_value;
    assign  mem_req_o.value     = data[mem_idx].rs2_value;

    // --------
    // COUNTERS
    // --------

    // Head counter pointing to the oldest store
    modn_counter #(
        .N (DEPTH)
    ) u_head_counter (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .en_i    (head_cnt_en   ),
        .clr_i   (head_cnt_clr  ),
        .count_o (head_idx      ),
        .tc_o    () // not needed
    );

    // Tail counter pointing to the first empty entry
    modn_counter #(
        .N (DEPTH)
    ) u_tail_counter (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .en_i    (tail_cnt_en   ),
        .clr_i   (tail_cnt_clr  ),
        .count_o (tail_idx      ),
        .tc_o    () // not needed
    );

    // Address counter pointing to the next instruction proceeding to address
    // computation
    modn_counter #(
        .N (DEPTH)
    ) u_addr_counter (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .en_i    (addr_cnt_en   ),
        .clr_i   (addr_cnt_clr  ),
        .count_o (addr_idx      ),
        .tc_o    () // not needed
    );

    // Memory access counter pointing to the next store performing a memory
    // request
    modn_counter #(
        .N (DEPTH )
    ) u_mem_counter (
        .clk_i   (clk_i       ),
        .rst_n_i (rst_n_i     ),
        .en_i    (mem_cnt_en  ),
        .clr_i   (mem_cnt_clr ),
        .count_o (mem_idx     ),
        .tc_o    () // not needed
    );

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    always @(posedge clk_i) begin
        foreach (curr_state[i]) begin
            assert property (@(posedge clk_i) disable iff (!rst_n_i) curr_state[i] == STORE_S_HALT |-> ##1 curr_state[i] != STORE_S_HALT);
        end
    end
    `endif /* SYNTHESIS */

endmodule