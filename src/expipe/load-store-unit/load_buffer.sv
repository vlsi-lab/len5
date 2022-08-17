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
// File: load_buffer.sv
// Author: Michele Caon
// Date: 15/07/2022

// LEN5 compilation switches
`include "len5_config.svh"

// Import UVM report macros
`include "uvm_macros.svh"
import uvm_pkg::*;
import len5_pkg::XLEN;
import len5_pkg::except_code_t;
import expipe_pkg::*;
import memory_pkg::*;;

/**
 * @brief	Bare-metal load buffer.
 *
 * @details	Load buffer without support for virtual memory (no TLB), intended
 *          to be directly connected to a memory module.
 */
module load_buffer #(
    parameter DEPTH = 4
) (
    input   logic                       clk_i,
    input   logic                       rst_n_i,
    input   logic                       flush_i,

    /* Issue stage */
    input   logic                       issue_valid_i,
    output  logic                       issue_ready_o,
    input   ldst_width_t                 issue_type_i,   // byte, halfword, ...
    input   op_data_t                   issue_rs1_i,    // base address
    input   logic [XLEN-1:0]            issue_imm_i,    // offset
    input   rob_idx_t                   issue_dest_rob_idx_i,

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

    /* Memory system */
    input   logic                       mem_valid_i,
    input   logic                       mem_ready_i,
    output  logic                       mem_valid_o,
    output  logic                       mem_ready_o,
    output  mem_req_t                   mem_req_o,
    input   mem_ans_t                   mem_ans_i

    /* Store buffer (store-to-load forwarding) */ /* TODO */
    // input   logic [STBUFF_IDX_LEN-1:0]  sb_pending_cnt_i,   // number of uncommitted store instructions
    // input   logic                       sb_committing_i,    // a store is committing
    // input   logic                       sb_hit_i,           // store data can be forwarded
    // input   logic [XLEN-1:0]            sb_value_i,         // store value
    // output  logic [XLEN-1:0]            sb_addr_o,          // load address
    // output  ldst_width_t                 sb_type_o,          // load type
    // output  logic [STBUFF_IDX_LEN:0]    sb_older_cnt_o,     // nummber of older store instructions
);
    // Load buffer data type
    // ---------------------
    
    /* Load instruction status */
    typedef enum logic [2:0] {
        LOAD_S_EMPTY,
        LOAD_S_RS1_PENDING,
        LOAD_S_ADDR_PENDING,
        LOAD_S_MEM_PENDING,
        LOAD_S_COMPLETED,
        LOAD_S_HALT     // for debug
    } lb_state_t;

    /* Load instruction data */
    typedef struct packed {
        ldst_width_t                 load_type;
        // logic [STBUFF_IDX_LEN-1:0]  older_stores;
        rob_idx_t                   rs1_rob_idx;
        logic [XLEN-1:0]            rs1_value;
        rob_idx_t                   dest_rob_idx;
        logic [XLEN-1:0]            imm_addr_value; // immediate offset, then replaced with resulting address
        logic                       except_raised;
        except_code_t               except_code;
        logic [XLEN-1:0]            value;
    } lb_data_t;

    /* Load instruction command */
    typedef enum logic [2:0] {
        LOAD_OP_NONE,
        LOAD_OP_PUSH,
        LOAD_OP_SAVE_RS1,
        LOAD_OP_SAVE_ADDR,
        LOAD_OP_SAVE_MEM
    } lb_op_t;

    // INTERNAL SIGNALS
    // ----------------

    // Head, tail, and address calculation counters
    logic [$clog2(DEPTH)-1:0]   head_idx, tail_idx, addr_idx, mem_idx;
    logic                       head_cnt_en, tail_cnt_en, addr_cnt_en, mem_cnt_en;
    logic                       head_cnt_clr, tail_cnt_clr, addr_cnt_clr, mem_cnt_clr;

    // Load buffer data
    lb_data_t       data[DEPTH];
    lb_state_t      curr_state[DEPTH], next_state[DEPTH];

    // Load buffer control
    logic           push, pop, save_rs1, save_addr, save_mem;
    lb_op_t         lb_op[DEPTH];

    // Byte selector
    logic [(XLEN>>3)-1:0]   byte_offs;
    logic [XLEN-1:0]        read_data;

    // -----------------
    // FIFO CONTROL UNIT
    // -----------------

    // Push, pop, save controls
    assign  push        = issue_valid_i && issue_ready_o;
    assign  pop         = cdb_valid_o && cdb_ready_i;
    assign  save_rs1    = cdb_valid_i;
    assign  save_addr   = adder_valid_i && adder_ready_o;  
    assign  save_mem    = mem_valid_i && mem_ready_o;
  
    // Counters control
    assign  head_cnt_clr    = flush_i;
    assign  tail_cnt_clr    = flush_i;
    assign  addr_cnt_clr    = flush_i;
    assign  mem_cnt_clr     = flush_i;
    assign  head_cnt_en     = pop;
    assign  tail_cnt_en     = push;
    assign  addr_cnt_en     = save_addr;
    assign  mem_cnt_en      = save_mem;

    // State progression
    // NOTE: Mealy to avoid sampling useless data
    always_comb begin : p_state_prog
        // Default operation
        foreach (lb_op[i]) lb_op[i] = LOAD_OP_NONE;

        foreach (curr_state[i]) begin
            case (curr_state[i])
                LOAD_S_EMPTY: begin // push
                    if (push && tail_idx == i) begin
                        lb_op[i]        = LOAD_OP_PUSH;
                        if (issue_rs1_i.ready)
                            next_state[i]   = LOAD_S_ADDR_PENDING;
                        else                    
                            next_state[i]   = LOAD_S_RS1_PENDING;
                    end else 
                        next_state[i] = LOAD_S_EMPTY; 
                end
                LOAD_S_RS1_PENDING: begin // save rs1 value from CDB
                    if (save_rs1 && cdb_data_i.rob_idx == data[i].rs1_rob_idx) begin 
                        lb_op[i]        = LOAD_OP_SAVE_RS1;
                        next_state[i]   = LOAD_S_ADDR_PENDING;
                    end else
                        next_state[i]   = LOAD_S_RS1_PENDING;
                end
                LOAD_S_ADDR_PENDING: begin // save address (from adder)
                    if (save_addr && adder_ans_i.tag == i) begin
                        lb_op[i]        = LOAD_OP_SAVE_ADDR;
                        if (adder_ans_i.except_raised)
                            next_state[i]   = LOAD_S_COMPLETED;
                        else
                            next_state[i]   = LOAD_S_MEM_PENDING;
                    end else
                        next_state[i]   = LOAD_S_ADDR_PENDING;
                end
                LOAD_S_MEM_PENDING: begin // save memory value (from memory)
                    if (save_mem && mem_ans_i.tag == i) begin
                        lb_op[i]        = LOAD_OP_SAVE_MEM;
                        next_state[i]   = LOAD_S_COMPLETED;
                    end else
                        next_state[i]   = LOAD_S_MEM_PENDING;
                end
                LOAD_S_COMPLETED: begin
                    if (pop && head_idx == i)
                        next_state[i]   = LOAD_S_EMPTY;
                    else 
                        next_state[i]   = LOAD_S_COMPLETED;
                end
                default: next_state[i]  = LOAD_S_HALT;
            endcase
        end
    end

    // State update
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : p_state_update
        if (!rst_n_i) foreach (curr_state[i]) curr_state[i] <= LOAD_S_EMPTY;
        else if (flush_i) foreach (curr_state[i]) curr_state[i] <= LOAD_S_EMPTY;
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
            foreach (lb_op[i]) begin
                case (lb_op[i])
                    LOAD_OP_PUSH: begin
                        data[i].load_type       <= issue_type_i;
                        data[i].rs1_rob_idx     <= issue_rs1_i.rob_idx;
                        data[i].rs1_value       <= issue_rs1_i.value;
                        data[i].dest_rob_idx    <= issue_dest_rob_idx_i;
                        data[i].imm_addr_value  <= issue_imm_i;
                        data[i].except_raised   <= 1'b0;
                    end
                    LOAD_OP_SAVE_RS1: begin
                        data[i].rs1_value       <= cdb_data_i.value;
                    end
                    LOAD_OP_SAVE_ADDR: begin
                        data[i].imm_addr_value  <= adder_ans_i.result;
                        data[i].except_raised   <= adder_ans_i.except_raised;
                        data[i].except_code     <= adder_ans_i.except_code;
                    end
                    LOAD_OP_SAVE_MEM: begin
                        data[i].value           <= read_data;
                        data[i].except_raised   <= mem_ans_i.except_raised;
                        data[i].except_code     <= mem_ans_i.except_code;
                    end
                    default:;
                endcase
            end
        end
    end

    // -----------------
    // OUTPUT EVALUATION
    // -----------------

    /* Issue stage */
    assign issue_ready_o   = curr_state[tail_idx] == LOAD_S_EMPTY;
    
    /* CDB */
    assign cdb_valid_o              = curr_state[head_idx] == LOAD_S_COMPLETED;
    assign cdb_data_o.rob_idx       = data[head_idx].dest_rob_idx;
    assign cdb_data_o.res_value     = data[head_idx].ld_value;
    assign cdb_data_o.res_aux       = '0;
    assign cdb_data_o.except_raised = data[head_idx].except_raised;
    assign cdb_data_o.except_code   = data[head_idx].except_code;

    /* Address adder */
    assign adder_valid_o           = curr_state[addr_idx] == LOAD_S_ADDR_PENDING;
    assign adder_ready_o           = 1'b1; // always ready to accept data from the adder
    assign adder_req_o.tag         = addr_idx;
    assign adder_req_o.is_store    = 1'b0;
    assign adder_req_o.ls_type     = data[addr_idx].load_type;
    assign adder_req_o.base        = data[addr_idx].rs1_value;
    assign adder_req_o.offs        = data[addr_idx].imm_addr_value;

    /* Memory system */
    assign mem_valid_o         = curr_state[mem_idx] == LOAD_S_MEM_PENDING;
    assign mem_ready_o         = 1'b1;
    assign mem_req_o.tag       = mem_idx;
    assign mem_req_o.acc_type  = MEM_ACC_LD;
    assign mem_req_o.ls_type   = data[mem_idx].load_type;
    assign mem_req_o.addr      = data[mem_idx].imm_addr_value;

    // -------------
    // BYTE SELECTOR
    // -------------
    // NOTE: the memory is expected to provide a doubleword regardless of
    //       the load width. This module extracts and sign-extends only the
    //       requested data from the fetched doubleword. 
    assign  byte_offs   = data[mem_ans_i.tag].imm_addr_value[2:0];
    byte_selector u_byte_selector (
    	.type_i   (data[mem_ans_i.tag].load_type ),
        .byte_off (byte_offs                     ),
        .data_i   (mem_ans_i.value               ),
        .data_o   (read_data                     )
    );

    // --------
    // COUNTERS
    // --------

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

    modn_counter #(
        .N (DEPTH)
    ) u_mem_counter (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .en_i    (mem_cnt_en    ),
        .clr_i   (mem_cnt_clr   ),
        .count_o (mem_idx       ),
        .tc_o    () // not needed
    );

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    always @(posedge clk_i) begin
        foreach (curr_state[i]) begin
            a_error: assert (curr_state[i] != LOAD_S_HALT)
                else `uvm_error("LOAD BUFFER", "CU in HALT state");
        end
    end
    `endif /* SYNTHESIS */

endmodule