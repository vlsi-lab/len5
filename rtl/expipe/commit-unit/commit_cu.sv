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

module commit_cu (
  // Clock and reset
  input logic clk_i,
  input logic rst_ni,

  // Commit logic <--> CU
  input  expipe_pkg::comm_type_t    comm_type_i,      // from commit decoder
  input  logic                      mispredict_i,     // branch misprediction
  output logic                      comm_reg_en_o,    // commit register enable
  output logic                      comm_reg_clr_o,   // commit register clear
  output expipe_pkg::comm_rd_sel_t  comm_rd_sel_o,    // rd is link address
  output logic                      comm_jb_instr_o,  // committing a jump/branch
  output expipe_pkg::comm_csr_sel_t comm_csr_sel_o,   // select PC as CSR data

  // ROB <--> CU
  input  logic                   valid_i,
  output logic                   ready_o,
  input  logic                   res_ready_i,
  input  len5_pkg::except_code_t except_code_i,

  // CU <--> integer register file and status
  output logic int_rs_valid_o,
  output logic int_rf_valid_o,

  // CU <--> floating-point register file and status
  // output logic fp_rs_valid_o,
  // output logic fp_rf_valid_o,

  // CU <--> CSRs
  output logic csr_valid_o,
  output logic csr_override_o,  // TODO: probably redundant with decoder
  output expipe_pkg::comm_csr_instr_t csr_comm_insn_o,  // committing instruction type
  output logic [csr_pkg::CSR_ADDR_LEN-1:0] csr_addr_o,

  // CU <--> others
  input  logic fe_ready_i,
  output logic fe_except_raised_o,
  output logic ex_mis_flush_o,      // flush execution pipeline after misprediction
  output logic except_flush_o,      // flush everything after exception
  output logic issue_resume_o       // resume after stall
);

  import len5_config_pkg::*;
  import len5_pkg::*;
  import expipe_pkg::*;
  import csr_pkg::*;
  import instr_pkg::*;

  // INTERNAL SIGNALS
  // ----------------

  // CU state type
  typedef enum logic [4:0] {
    RESET,
    IDLE,                // wait for a valid instruction from the ROB
    COMMIT_INT_RF,       // commit to the integer RF
    COMMIT_FP_RF,        // commit to the floating-point RF
    COMMIT_LOAD,         // commit load isntructions
    COMMIT_STORE,        // commit store instructions
    COMMIT_JUMP,         // commit jump-and-link instructions
    COMMIT_JUMP_MIS,     // flush the pipeline after misprediction
    COMMIT_BRANCH,       // commit correctly predicted branch instructions
    COMMIT_BRANCH_MIS,   // handle branch misprediction
    COMMIT_CSR,          // commit to CSRs
    COMMIT_FENCE,        // commit fence instructions
    COMMIT_ECALL,        // commit ECALL instructions
    COMMIT_EBREAK,       // commit EBREAK instructions
    INT_WRITE_CODE,      // write the interrupt exception code to mcause
    COMMIT_MRET,         // commit MRET instructions
    MRET_LOAD_PC,        // load the PC in mepc
    COMMIT_WFI,          // wait for interrupt
    COMMIT_EXCEPT,       // handle the generated exception
    EXCEPT_LOAD_PC,      // load exception handling program counter
    EXCEPT_WRITE_CODE,   // write exception code to mcause
    EXCEPT_SAVE_ADDR,    // save faulting memory address to mtval
    EXCEPT_SAVE_INSTR,   // save faulting instruction to mtval
    EXCEPT_CLEAR_MTVAL,  // save zero to mtval
    CLEAR_COMM_REG,      // clear the commit register
    ISSUE_RESUME,        // resume execution after stall

    HALT  // dead-end state
  } cu_state_t;

  // CU current and next states
  cu_state_t curr_state, v_next_state, next_state;

  // ------------
  // CONTROL UNIT
  // ------------
  // NOTE: to avoid recomputing the next state in each state, the next state
  //       on valid input is computed by a dedicated combinational network.
  //       Special cases are handled by the CU's state progression network.

  // Next state on valid instruction
  always_comb begin : cu_next_state
    case (comm_type_i)
      COMM_TYPE_NONE:   v_next_state = IDLE;
      COMM_TYPE_INT_RF: begin
        if (res_ready_i) v_next_state = COMMIT_INT_RF;
        else v_next_state = HALT;
      end
      // COMM_TYPE_FP_RF: begin
      //   if (res_ready_i) v_next_state = COMMIT_FP_RF;
      //   else v_next_state = HALT;
      // end
      COMM_TYPE_LOAD: begin
        if (res_ready_i) v_next_state = COMMIT_LOAD;
        else v_next_state = HALT;
      end
      COMM_TYPE_STORE: begin
        // NOTE: the memory access is performed before commit if
        // the store is not speculative (i.e., all previous jumps
        // or branches have been resolved and committed).
        if (res_ready_i) v_next_state = COMMIT_STORE;
        else v_next_state = HALT;
      end
      COMM_TYPE_JUMP: begin
        if (mispredict_i) v_next_state = COMMIT_JUMP_MIS;
        else v_next_state = COMMIT_JUMP;
      end
      COMM_TYPE_BRANCH: begin
        if (mispredict_i) v_next_state = COMMIT_BRANCH_MIS;
        else v_next_state = COMMIT_BRANCH;
      end
      COMM_TYPE_CSR:    v_next_state = COMMIT_CSR;
      COMM_TYPE_FENCE:  v_next_state = COMMIT_FENCE;
      COMM_TYPE_ECALL:  v_next_state = COMMIT_ECALL;
      COMM_TYPE_EBREAK: v_next_state = COMMIT_EBREAK;
      COMM_TYPE_MRET:   v_next_state = COMMIT_MRET;
      COMM_TYPE_WFI:    v_next_state = COMMIT_WFI;
      COMM_TYPE_EXCEPT: v_next_state = COMMIT_EXCEPT;
      default:          v_next_state = RESET;
    endcase
  end

  // State progression
  always_comb begin : cu_state_prog
    case (curr_state)
      // Reset state
      RESET: next_state = IDLE;
      // Idle: wait for a valid instruction
      IDLE: begin
        if (valid_i) next_state = v_next_state;
        else next_state = IDLE;
      end
      // Commit to the integer register file
      COMMIT_INT_RF: begin
        if (valid_i) next_state = v_next_state;
        else next_state = IDLE;
      end
      // Commit load instructions
      COMMIT_LOAD: begin
        if (valid_i) next_state = v_next_state;
        else next_state = IDLE;
      end

      // Commit to the floating-point register file
      // COMMIT_FP_RF: begin
      //   if (valid_i) next_state = v_next_state;
      //   else next_state = IDLE;
      // end

      // Commit store instructions
      COMMIT_STORE: begin
        if (valid_i) next_state = v_next_state;
        else next_state = IDLE;
      end
      // Commit jump instructions
      COMMIT_JUMP: begin
        if (valid_i) next_state = v_next_state;
        else next_state = IDLE;
      end
      // Commit jump with mispredition
      COMMIT_JUMP_MIS:    next_state = IDLE;
      // Correctly predicted branch: just commit
      COMMIT_BRANCH: begin
        if (valid_i) next_state = v_next_state;
        else next_state = IDLE;
      end
      // Flush the in-flight instructions
      COMMIT_BRANCH_MIS:  next_state = IDLE;
      // Atomically read and write CSRs
      COMMIT_CSR:         next_state = IDLE;
      /* TODO: properly handle the following instructions */
      COMMIT_FENCE:       next_state = IDLE;
      COMMIT_ECALL:       next_state = INT_WRITE_CODE;
      INT_WRITE_CODE:     next_state = EXCEPT_LOAD_PC;
      COMMIT_EBREAK:      next_state = IDLE;
      COMMIT_MRET:        next_state = MRET_LOAD_PC;
      MRET_LOAD_PC: begin
        if (fe_ready_i) next_state = IDLE;
        else next_state = MRET_LOAD_PC;
      end
      COMMIT_WFI:         next_state = IDLE;
      // Flush the in-flight instructions
      COMMIT_EXCEPT:      next_state = EXCEPT_WRITE_CODE;
      EXCEPT_WRITE_CODE: begin
        unique case (except_code_i)
          // Access faults: save offending address
          E_I_ADDR_MISALIGNED,
                    E_I_ACCESS_FAULT,
                    E_BREAKPOINT,
                    E_LD_ADDR_MISALIGNED,
                    E_LD_ACCESS_FAULT,
                    E_ST_ADDR_MISALIGNED,
                    E_ST_ACCESS_FAULT,
                    E_INSTR_PAGE_FAULT,
                    E_LD_PAGE_FAULT,
                    E_ST_PAGE_FAULT:
          next_state = EXCEPT_SAVE_ADDR;
          // Illegal instruction: save instruction
          E_ILLEGAL_INSTRUCTION: next_state = EXCEPT_SAVE_INSTR;
          // Others: clear mtval
          default: next_state = EXCEPT_CLEAR_MTVAL;
        endcase
      end
      // Save esception data to mtval and return load ESR PC
      EXCEPT_SAVE_ADDR:   next_state = EXCEPT_LOAD_PC;
      EXCEPT_SAVE_INSTR:  next_state = EXCEPT_LOAD_PC;
      EXCEPT_CLEAR_MTVAL: next_state = EXCEPT_LOAD_PC;
      // Load the exception handler PC
      EXCEPT_LOAD_PC: begin
        if (fe_ready_i) next_state = CLEAR_COMM_REG;
        else next_state = EXCEPT_LOAD_PC;
      end
      // Clear the commit register and return to IDLE
      CLEAR_COMM_REG:     next_state = IDLE;
      // HALT state (deadlock)
      HALT:               next_state = HALT;
      // Unexpected state
      default:            next_state = RESET;
    endcase
  end

  // Output evaluation
  always_comb begin : cu_out_eval
    // Default values
    ready_o            = 1'b0;
    comm_reg_en_o      = 1'b0;
    comm_reg_clr_o     = 1'b0;
    comm_rd_sel_o      = COMM_RD_SEL_RES;
    comm_jb_instr_o    = 1'b0;
    comm_csr_sel_o     = COMM_CSR_SEL_RES;
    csr_override_o     = 1'b0;
    csr_addr_o         = CSR_MEPC;
    int_rs_valid_o     = 1'b0;
    int_rf_valid_o     = 1'b0;
    // fp_rs_valid_o = 1'b0;
    // fp_rf_valid_o = 1'b0;
    csr_valid_o        = 1'b0;
    csr_comm_insn_o    = COMM_CSR_INSTR_TYPE_NONE;
    fe_except_raised_o = 1'b0;
    ex_mis_flush_o     = 1'b0;
    except_flush_o     = 1'b0;
    issue_resume_o     = 1'b0;

    case (curr_state)
      RESET: ;  // default

      IDLE: begin
        ready_o       = 1'b1;
        comm_reg_en_o = 1'b1;
      end
      COMMIT_INT_RF: begin
        ready_o         = 1'b1;
        int_rs_valid_o  = 1'b1;
        int_rf_valid_o  = 1'b1;
        comm_reg_en_o   = 1'b1;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_INT;
      end

      // COMMIT_FP_RF: begin
      // ready_o         = 1'b1;
      // fp_rs_valid_o   = 1'b1;
      // fp_rf_valid_o   = 1'b1;
      // comm_reg_en_o   = 1'b1;
      // csr_comm_insn_o = COMM_CSR_INSTR_TYPE_OTHER;
      // end

      COMMIT_LOAD: begin
        ready_o         = 1'b1;
        int_rs_valid_o  = 1'b1;
        int_rf_valid_o  = 1'b1;
        comm_reg_en_o   = 1'b1;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_LOAD;
      end

      COMMIT_STORE: begin
        ready_o         = 1'b1;
        comm_reg_en_o   = 1'b1;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_STORE;
      end
      COMMIT_JUMP: begin
        ready_o         = 1'b1;
        int_rs_valid_o  = 1'b1;
        int_rf_valid_o  = 1'b1;
        comm_reg_en_o   = 1'b1;
        comm_jb_instr_o = 1'b1;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_JUMP;
      end
      COMMIT_JUMP_MIS: begin
        int_rs_valid_o  = 1'b1;
        int_rf_valid_o  = 1'b1;
        comm_reg_clr_o  = 1'b1;
        ex_mis_flush_o  = 1'b1;
        comm_jb_instr_o = 1'b1;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_JUMP;
        issue_resume_o  = 1'b1;
      end
      COMMIT_BRANCH: begin
        ready_o         = 1'b1;
        comm_reg_en_o   = 1'b1;
        comm_jb_instr_o = 1'b1;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_BRANCH;
      end
      COMMIT_BRANCH_MIS: begin
        ex_mis_flush_o  = 1'b1;
        comm_reg_clr_o  = 1'b1;
        comm_jb_instr_o = 1'b1;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_BRANCH;
        issue_resume_o  = 1'b1;
      end
      CLEAR_COMM_REG: begin
        comm_reg_clr_o = 1'b1;
      end
      COMMIT_CSR: begin
        int_rf_valid_o  = 1'b1;
        int_rs_valid_o  = 1'b1;
        csr_valid_o     = 1'b1;
        comm_reg_en_o   = 1'b1;
        comm_rd_sel_o   = COMM_RD_SEL_CSR;
        issue_resume_o  = 1'b1;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_OTHER;
      end

      /* TODO: properly handle the following instructions */
      COMMIT_FENCE: begin
        comm_reg_en_o   = 1'b1;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_OTHER;
      end
      COMMIT_ECALL: begin
        csr_valid_o     = 1'b1;  // save PC to mepc
        csr_override_o  = 1'b1;
        csr_addr_o      = CSR_MEPC;
        comm_csr_sel_o  = COMM_CSR_SEL_PC;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_OTHER;
      end
      INT_WRITE_CODE: begin
        csr_valid_o    = 1'b1;  // save exception code to mcause
        csr_override_o = 1'b1;
        csr_addr_o     = CSR_MCAUSE;
        comm_csr_sel_o = COMM_CSR_SEL_INT;
        comm_reg_en_o  = 1'b1;
      end
      COMMIT_EBREAK: begin
        comm_reg_en_o   = 1'b1;
        ex_mis_flush_o  = 1'b1;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_OTHER;
      end
      COMMIT_MRET: begin  // read mepc
        csr_override_o  = 1'b1;
        csr_addr_o      = CSR_MEPC;
        comm_csr_sel_o  = COMM_CSR_SEL_ZERO;
        comm_reg_en_o   = 1'b1;
        ex_mis_flush_o  = 1'b1;
        except_flush_o  = 1'b1;  // also flush relevant data
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_OTHER;
      end
      MRET_LOAD_PC: begin
        csr_override_o     = 1'b1;
        csr_addr_o         = CSR_MEPC;
        comm_csr_sel_o     = COMM_CSR_SEL_ZERO;
        fe_except_raised_o = 1'b1;
        issue_resume_o     = 1'b1;
      end
      COMMIT_WFI: begin
        comm_reg_en_o   = 1'b1;
        csr_comm_insn_o = COMM_CSR_INSTR_TYPE_OTHER;
      end
      COMMIT_EXCEPT: begin
        csr_valid_o    = 1'b1;
        csr_override_o = 1'b1;
        csr_addr_o     = CSR_MEPC;
        comm_csr_sel_o = COMM_CSR_SEL_PC;
        ex_mis_flush_o = 1'b1;
        except_flush_o = 1'b1;
      end
      EXCEPT_WRITE_CODE: begin
        csr_valid_o    = 1'b1;  // save exception code to mcause
        csr_override_o = 1'b1;
        csr_addr_o     = CSR_MCAUSE;
        comm_csr_sel_o = COMM_CSR_SEL_EXCEPT;
      end
      EXCEPT_SAVE_ADDR: begin
        comm_reg_en_o  = 1'b1;
        csr_override_o = 1'b1;
        csr_addr_o     = CSR_MTVAL;
        comm_csr_sel_o = COMM_CSR_SEL_RES;  // faulting address inside instruction result
        comm_rd_sel_o  = COMM_RD_SEL_CSR;
      end
      EXCEPT_SAVE_INSTR: begin
        comm_reg_en_o  = 1'b1;
        csr_override_o = 1'b1;
        csr_addr_o     = CSR_MTVAL;
        comm_csr_sel_o = COMM_CSR_SEL_INSN;
      end
      EXCEPT_CLEAR_MTVAL: begin
        comm_reg_en_o  = 1'b1;
        csr_override_o = 1'b1;
        csr_addr_o     = CSR_MTVAL;
        comm_csr_sel_o = COMM_CSR_SEL_ZERO;
      end
      EXCEPT_LOAD_PC: begin
        fe_except_raised_o = 1'b1;
        comm_rd_sel_o      = COMM_RD_SEL_EXCEPT;
        issue_resume_o     = 1'b1;
      end

      HALT:    ;
      default: ;
    endcase
  end

  // State update
  always_ff @(posedge clk_i or negedge rst_ni) begin : cu_state_upd
    if (!rst_ni) curr_state <= RESET;
    else curr_state <= next_state;
  end

  // ----------
  // DEBUG CODE
  // ----------
`ifndef SYNTHESIS
`ifndef VERILATOR
  always @(posedge clk_i) begin
    $display("valid_i: %b | type: %s | state: %s", valid_i, comm_type_i.name(), curr_state.name());
  end
`endif  /* VERILATOR */
`endif  /* SYNTHESIS */

endmodule
