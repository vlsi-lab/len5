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
// File: commit_decoder.sv
// Author: Michele Caon
// Date: 20/11/2019

// THIS FILE IS ONYL A TEMPLATE, THE COMMIT LOGIC IS NOT IMPLEMENTED YET, SINCE IT REQUIRES ALL THE PROCESSOR PARTS TO BE FUNCTIONAL

module commit_decoder (
  // Data from the commit logic
  input  len5_pkg::instr_t       instruction_i,
  input  logic                   except_raised_i,
  // Control to the commit logic
  output expipe_pkg::comm_type_t comm_type_o
);

  import len5_pkg::ILEN;
  import len5_pkg::OPCODE_LEN;
  import expipe_pkg::*;
  import csr_pkg::*;
  import instr_pkg::*;
  // INTERNAL SIGNALS
  // ----------------
  comm_type_t comm_type;

  // --------------------
  // COMMIT DOCODER LOGIC
  // --------------------
  // Main opcode decoder
  always_comb begin : comm_decoder
    // Default
    comm_type = COMM_TYPE_NONE;

    // Hanle exceptions
    if (except_raised_i) comm_type = COMM_TYPE_EXCEPT;

    // No exceptions raised
    else begin
      case (instruction_i.raw)
        // Intructions committing to the integer RF
        // ----------------------------------------
        ADD, ADDI, ADDIW, ADDW,
        SUB, SUBW,
        AND, ANDI, OR, ORI, XOR, XORI,
        SLL, SLLI, SLLIW, SLLW, SLT, SLTI, SLTIU, SLTU,
        SRA, SRAI, SRAIW, SRAW, SRL, SRLI, SRLIW, SRLW,
        MUL, MULH, MULHSU, MULHU, MULW,
        REM, REMU, REMUW, REMW,
        DIV, DIVU, DIVUW, DIVW,
        LUI, AUIPC
        :
        comm_type = COMM_TYPE_INT_RF;

        LB, LBU, LD, LH, LHU, LUI, LW, LWU: comm_type = COMM_TYPE_LOAD;

        // Store instructions
        // ------------------
        SB, SD, SH: comm_type = COMM_TYPE_STORE;

        // Jump instructions
        // -----------------
        JAL, JALR: comm_type = COMM_TYPE_JUMP;

        // Branch instructions
        // -------------------
        BEQ, BGE, BGEU, BLT, BLTU, BNE: comm_type = COMM_TYPE_BRANCH;

        // CSR instructions
        // ----------------
        CSRRC, CSRRCI, CSRRS, CSRRSI, CSRRW, CSRRWI: comm_type = COMM_TYPE_CSR;

        // ECALL, EBREAK
        // -------------
        ECALL:  comm_type = COMM_TYPE_ECALL;
        EBREAK: comm_type = COMM_TYPE_EBREAK;

        // MRET, WFI
        // ---------
        MRET: comm_type = COMM_TYPE_MRET;
        WFI:  comm_type = COMM_TYPE_WFI;

        // FENCE
        // -----
        FENCE: comm_type = COMM_TYPE_FENCE;

        default: comm_type = COMM_TYPE_EXCEPT;
      endcase
    end
  end

  // -----------------
  // OUTPUT EVALUATION
  // -----------------
  // Commit type MUX
  assign comm_type_o = comm_type;

endmodule
