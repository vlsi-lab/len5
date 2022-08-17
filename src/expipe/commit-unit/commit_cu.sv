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
// File: commit_cu.sv
// Author: Michele Caon
// Date: 25/11/2021

// Include LEN5 configuration
`include "len5_config.svh"

/* Include UVM macros */
`include "uvm_macros.svh"

/* Import UVM package */
import uvm_pkg::*;

import len5_pkg::ILEN;
import len5_pkg::instr_t;
import len5_pkg::except_code_t;
import expipe_pkg::*;
import csr_pkg::*;

module commit_cu (
    // Clock and reset
    input   logic                   clk_i,
    input   logic                   rst_n_i,

    // Commit logic <--> CU
    input   comm_type_t             comm_type_i,    // from commit decoder
    input   logic                   store_comm_i,   // a store instruction is ready to commit
    input   logic                   mispredict_i,   // branch misprediction
    output  logic                   comm_reg_en_o,  // commit enable
    output  logic                   is_jump_o,      // the committing is a jump

    // ROB <--> CU
    input   logic                   valid_i,
    output  logic                   ready_o,

    input   instr_t                 instr_i,
    input   logic                   res_ready_i,
    input   logic                   except_raised_i,
    input   except_code_t           except_code_i,

    // CU <--> integer register file and status
    // input   logic                   int_rs_ready_i,
    output  logic                   int_rs_valid_o,
    // input   logic                   int_rf_ready_i,
    output  logic                   int_rf_valid_o,

`ifdef LEN5_FP_EN
    // CU <--> floating-point register file and status
    // input   logic                   fp_rs_ready_i,
    output  logic                   fp_rs_valid_o,
    // input   logic                   fp_rf_ready_i,
    output  logic                   fp_rf_valid_o,
`endif /* LEN5_FP_EN */

    // CU <--> store buffer
    output  logic                   sb_pop_store_o, // pop the store instruction from the store buffer

    // CU <--> CSRs
    // input   logic                   csr_ready_i,
    output  logic                   csr_valid_o,
    output  csr_instr_t             csr_type_o,

    // CU <--> others
    output  logic                   fe_res_valid_o,
    output  logic                   flush_o,
    output  logic                   resume_o    // to the main CU
);

    // INTERNAL SIGNALS
    // ----------------

    // CU state type
    typedef enum logic [4:0] {
        RESET,
        IDLE,               // wait for a valid instruction from the ROB
        COMMIT_INT_RF,      // commit to the integer RF
        COMMIT_FP_RF,       // commit to the floating-point RF
        COMMIT_STORE,       // commit store instructions
        WAIT_STORE,         // wait for a store instruction to commit from the store buffer
        COMMIT_JUMP,        // commit jump-and-link instructions
        COMMIT_JUMP_MIS,    // commit jumps and restart
        COMMIT_BRANCH,      // commit correctly predicted branch instructions
        MIS_FLUSH,          // handle branch misprediction
        MIS_LOAD_PC,        // load correct PC after misprediction
        COMMIT_CSR,         // commit to CSRs
        COMMIT_FENCE,       // commit fence instructions
        COMMIT_ECALL,       // commit ECALL instructions
        COMMIT_EBREAK,      // commit EBREAK instructions
        COMMIT_XRET,        // commit xRET instructions
        COMMIT_WFI,         // wait for interrupt
        COMMIT_EXCEPT,      // handle the generated exception

        HALT                // dead-end state
    } cu_state_t;

    // CU current and next states
    cu_state_t      curr_state, v_next_state, next_state;

    // ------------
    // CONTROL UNIT
    // ------------
    // NOTE: to avoid recomputing the next state in each state, the next state
    //       on valid input is computed by a dedicated combinational network.
    //       Special cases are handled by the CU's state progression network.

    // Next state on valid instruction
    always_comb begin : cu_next_state
        case (comm_type_i)
            COMM_TYPE_NONE:         v_next_state  = IDLE;
            COMM_TYPE_INT_RF:   begin
                if (res_ready_i)    v_next_state  = COMMIT_INT_RF;
                else                v_next_state  = HALT;
            end
        `ifdef LEN5_FP_EN
            COMM_TYPE_FP_RF:        begin
                if (res_ready_i)    v_next_state  = COMMIT_FP_RF;
                else                v_next_state  = HALT;
            end
        `endif /* LEN5_FP_EN */
            COMM_TYPE_STORE: begin
                if (!store_comm_i)  v_next_state  = WAIT_STORE;
                else                v_next_state  = COMMIT_STORE;
            end
            COMM_TYPE_JUMP: begin
                if (mispredict_i)   v_next_state  = COMMIT_JUMP_MIS;
                esle                v_next_state  = COMMIT_JUMP;
            end
            COMM_TYPE_BRANCH: begin
                if (mispredict_i)   v_next_state  = MIS_FLUSH;
                else                v_next_state  = COMMIT_BRANCH;
            end
            COMM_TYPE_CSR:          v_next_state  = COMMIT_CSR;
            COMM_TYPE_FENCE:        v_next_state  = COMMIT_FENCE;
            COMM_TYPE_ECALL:        v_next_state  = COMMIT_ECALL;
            COMM_TYPE_EBREAK:       v_next_state  = COMMIT_EBREAK;
            COMM_TYPE_XRET:         v_next_state  = COMMIT_XRET;
            COMM_TYPE_WFI:          v_next_state  = COMMIT_WFI;
            COMM_TYPE_EXCEPT:       v_next_state  = COMMIT_EXCEPT;
            default:                v_next_state  = RESET;
        endcase
    end

    // State progression
    always_comb begin : cu_state_prog
        case (curr_state)
            // Reset state
            RESET:              next_state  = IDLE;

            // Idle: wait for a valid instruction
            IDLE: begin
                if (valid_i)    next_state  = v_next_state;
                else            next_state  = IDLE;
            end

            // Commit to the integer register file
            // NOTE: do not wait for ready, the RFs are always ready
            COMMIT_INT_RF: begin
                if (valid_i)    next_state  = v_next_state;
                else            next_state  = IDLE;
            end

        `ifdef LEN5_FP_EN
            // Commit to the floating-point register file
            // NOTE: do not wait for ready, the RFs are always ready
            COMMIT_FP_RF: begin
                if (valid_i)    next_state  = v_next_state;
                else            next_state  = IDLE;
            end
        `endif /* LEN5_FP_EN */

            // Commit store instructions
            COMMIT_STORE: begin
                if (valid_i)    next_state  = v_next_state;
                else            next_state  = IDLE;
            end

            // Wait for store committing
            WAIT_STORE: begin
                if (!store_comm_i)  next_state  = WAIT_STORE;
                else                next_state  = COMMIT_STORE;
            end

            // Commit jump instructions
            COMMIT_JUMP: begin
                if (valid_i)    next_state  = v_next_state;
                else            next_state  = IDLE;
            end

            // Commit jump with mispredition
            COMMIT_JUMP_MIS:
                if (valid_i)    next_state  = v_next_state;
                else            next_state  = IDLE;

            // Correctly predicted branch: just commit
            COMMIT_BRANCH: begin
                if (valid_i)    next_state  = v_next_state;
                else            next_state  = IDLE;
            end

            // Flush the in-flight instructions
            MIS_FLUSH:      next_state  = MIS_LOAD_PC;

            // Load the correct PC and restart execution
            MIS_LOAD_PC:    next_state  = IDLE;

            // Atomically read and write CSRs
            COMMIT_CSR: begin
                if (valid_i)    next_state  = v_next_state;
                else            next_state  = IDLE;
            end

            /* TODO: properly handle the following instructions */
            COMMIT_FENCE:       next_state  = IDLE;
            COMMIT_ECALL:       next_state  = IDLE;
            COMMIT_EBREAK:      next_state  = IDLE;
            COMMIT_XRET:        next_state  = IDLE;
            COMMIT_WFI:         next_state  = IDLE;
            COMMIT_EXCEPT:      next_state  = IDLE;

            // HALT state (deadlock)
            HALT:               next_state  = HALT;

            // Unexpected state
            default:            next_state  = RESET;
        endcase
    end

    // Output evaluation
    always_comb begin : cu_out_eval
        // Default values
        ready_o             = 1'b0;
        comm_reg_en_o       = 1'b0;
        is_jump_o           = 1'b0;
        int_rs_valid_o      = 1'b0;
        int_rf_valid_o      = 1'b0;
    `ifdef LEN5_FP_EN
        fp_rs_valid_o       = 1'b0;
        fp_rf_valid_o       = 1'b0;
    `endif /* LEN5_FP_EN */
        sb_pop_store_o      = 1'b0;
        csr_valid_o         = 1'b0;
        csr_type_o          = CSR_INSTR;
        fe_res_valid_o      = 1'b0;
        flush_o             = 1'b0;
        resume_o            = 1'b0;

        case (curr_state)
            RESET:; // default

            IDLE: begin
                ready_o         = 1'b1;
                comm_reg_en_o   = 1'b1;
            end

            COMMIT_INT_RF: begin
                ready_o         = 1'b1;
                int_rs_valid_o  = 1'b1;
                int_rf_valid_o  = 1'b1;
                comm_reg_en_o   = 1'b1;
            end

        `ifdef LEN5_FP_EN
            COMMIT_FP_RF: begin
                ready_o         = 1'b1;
                fp_rs_valid_o   = 1'b1;
                fp_rf_valid_o   = 1'b1;
                comm_reg_en_o   = 1'b1;
            end
        `endif /* LEN5_FP_EN */

            COMMIT_STORE: begin
                ready_o         = 1'b1;
                sb_pop_store_o  = 1'b1;
                comm_reg_en_o   = 1'b1;
            end

            WAIT_STORE:; // use default values

            COMMIT_JUMP: begin
                ready_o         = 1'b1;
                int_rf_valid_o  = 1'b1;
                int_rs_valid_o  = 1'b1;
                comm_reg_en_o   = 1'b1;
                is_jump_o       = 1'b1;
                fe_res_valid_o  = 1'b1;
            end

            COMMIT_JUMP_MIS: begin
                int_rf_valid_o  = 1'b1;
                int_rs_valid_o  = 1'b1;
                is_jump_o       = 1'b1;
                fe_res_valid_o  = 1'b1;
                flush_o         = 1'b1;
            end

            COMMIT_BRANCH: begin
                ready_o         = 1'b1;
                comm_reg_en_o   = 1'b1;
            end

            MIS_FLUSH: begin
                flush_o         = 1'b1;
            end

            MIS_LOAD_PC: begin
                resume_o        = 1'b1;
            end

            COMMIT_CSR: begin
                csr_valid_o     = 1'b1;
                comm_reg_en_o   = 1'b1;
            end

            /* TODO: properly handle the following instructions */
            COMMIT_FENCE: begin
                comm_reg_en_o   = 1'b1;
            end
            COMMIT_ECALL: begin
                comm_reg_en_o   = 1'b1;
            end
            COMMIT_EBREAK: begin
                comm_reg_en_o   = 1'b1;
            end
            COMMIT_XRET: begin
                comm_reg_en_o   = 1'b1;
            end
            COMMIT_WFI: begin
                comm_reg_en_o   = 1'b1;
            end
            COMMIT_EXCEPT: begin
                comm_reg_en_o   = 1'b1;
            end

            HALT:;
            default:;
        endcase
    end

    // State update
    always_ff @( posedge clk_i or negedge rst_n_i ) begin : cu_state_upd
        if (!rst_n_i)       curr_state  <= RESET;
        else                curr_state  <= next_state;
    end
    
    // ----------
    // DEBUG CODE
    // ----------
    `ifndef SYNTHESIS
    always @(posedge clk_i) begin
        `uvm_info("COMMIT CU", $sformatf("valid_i: %b | instr: %h | type: %s | state: %s", valid_i, instr_i, comm_type_i.name(), curr_state), UVM_INFO)
    end
    `endif /* SYNTHESIS */

endmodule