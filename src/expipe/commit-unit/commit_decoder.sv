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

/* Include instruction macros */
`include "instr_macros.svh"

import expipe_pkg::*;
import len5_pkg::ILEN;
import len5_pkg::OPCODE_LEN;
import len5_pkg::instr_t;

module commit_decoder 
(
    // Data from the commit logic
    input   instr_t                 instruction_i,
	input   logic                   except_raised_i,

    // Control to the commit logic
    output  comm_type_t             comm_type_o
);

    // DEFINITIONS
    logic [OPCODE_LEN-1:0]          instr_opcode = instruction_i.r.opcode;

    // --------------------
    // COMMIT DOCODER LOGIC
    // --------------------
    always_comb begin: comm_decoder
        // Default
        comm_type_o     = COMM_TYPE_NONE;

        // Hanle exceptions
        if (except_raised_i)    comm_type_o = COMM_TYPE_EXCEPT;

        // No exceptions raised
        else begin
            case (instr_opcode)

                // Intructions committing to the integer RF
                // ----------------------------------------
                `OPCODE_ADDI,
                `OPCODE_LUI,
                `OPCODE_AUIPC,
                `OPCODE_LB,
                `OPCODE_LH,
                `OPCODE_LW,
                `OPCODE_LD,
                `OPCODE_LBU,
                `OPCODE_LHU,
                `OPCODE_LWU,
                `OPCODE_ADDI,
                `OPCODE_ADDIW,
                `OPCODE_SLTI,
                `OPCODE_SLTIU,
                `OPCODE_XORI,
                `OPCODE_ORI,
                `OPCODE_ANDI,
                `OPCODE_SLLIW,
                `OPCODE_SLLI,
                `OPCODE_SRLIW,
                `OPCODE_SRLI,
                `OPCODE_SRAIW,
                `OPCODE_SRAI,
                `OPCODE_ADDW,
                `OPCODE_SUBW,
                `OPCODE_ADD,
                `OPCODE_SUB,
                `OPCODE_SLLW,
                `OPCODE_SLL,
                `OPCODE_SLT,
                `OPCODE_SLTU,
                `OPCODE_XOR,
                `OPCODE_SRLW,
                `OPCODE_SRL,
                `OPCODE_SRAW,
                `OPCODE_SRA,
                `OPCODE_OR,
            `ifndef LEN5_M_EN
                `OPCODE_MUL,
                `OPCODE_MULW,
                `OPCODE_MULH,
                `OPCODE_MULHSU,
                `OPCODE_MULHU,
            `endif /* LEN5_M_EN */
                `OPCODE_AND:    comm_type_o      = COMM_TYPE_INT_RF;

                // Store instructions
                // ------------------
                `OPCODE_SB,
                `OPCODE_SH,
                `OPCODE_SW,
                `OPCODE_SD:     comm_type_o     = COMM_TYPE_STORE;

                // Jump instructions
                // ----------------- 
                `OPCODE_JAL,
                `OPCODE_JALR:   comm_type_o     = COMM_TYPE_JUMP;
                
                // Branch instructions
                // -------------------
                `OPCODE_BEQ,
                `OPCODE_BNE,
                `OPCODE_BLT,
                `OPCODE_BGE,
                `OPCODE_BLTU,
                `OPCODE_BGEU:   comm_type_o     = COMM_TYPE_BRANCH;

                // CSR instructions
                // ----------------
                `OPCODE_CSRRW,
                `OPCODE_CSRRS,
                `OPCODE_CSRRC,
                `OPCODE_CSRRWI,
                `OPCODE_CSRRSI,
                `OPCODE_CSRRCI: comm_type_o     = COMM_TYPE_CSR;

                // Fence instructions
                // ------------------
                `OPCODE_FENCE,
            `ifdef LEN5_PRIVILEGED_EN
                `OPCODE_SFENCE_VMA,
                `OPCODE_HFENCE_BVMA,
                `OPCODE_HFENCE_GVMA,
            `endif /* LEN5_PRIVILEGED_EN */
                `OPCODE_FENCE_I:    comm_type_o = COMM_TYPE_FENCE;

                // ECALL instructions
                // ------------------
                `OPCODE_ECALL:  comm_type_o     = COMM_TYPE_ECALL;

                // EBREAK instructions
                // -------------------
                `OPCODE_EBREAK: comm_type_o     = COMM_TYPE_EBREAK;
                
                // XRET instructions
                // -----------------
            `ifdef LEN5_PRIVILEGED_EN
                `OPCODE_URET,
                `OPCODE_SRET,
                `OPCODE_MRET:   comm_type_o     = COMM_TYPE_XRET;

                `OPCODE_WFI:    comm_type_o     = COMM_TYPE_WFI;
            `endif /* LEN5_PRIVILEGED_EN */

                // Ignore unsupported instructions (exception generated by issue)
                default:        comm_type_o     = COMM_TYPE_NONE;
            endcase
        end
    end
    
endmodule
