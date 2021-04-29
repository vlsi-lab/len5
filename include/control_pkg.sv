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
// File: control_pkg.sv
// Author: Michele Caon
// Date: 12/11/2019

`ifndef CONTROL_PKG
`define CONTROL_PKG

package control_pkg;

    import len5_pkg::XLEN;

    `define OPCODE_LEN 7
    `define FUNCT3_LEN 3
    `define FUNCT7_LEN 7

    //-----------------------------\\
    //----- INSTRUCTION CODES -----\\
    //-----------------------------\\

    // OPCODE: all instructions 
    // RV64I
    `define OPCODE_ADD          `OPCODE_LEN'b0110011
    `define OPCODE_ADDI         `OPCODE_LEN'b0010011
    `define OPCODE_ADDIW        `OPCODE_LEN'b0011011
    `define OPCODE_ADDW         `OPCODE_LEN'b0111011
    `define OPCODE_AND          `OPCODE_LEN'b0110011
    `define OPCODE_ANDI         `OPCODE_LEN'b0010011
    `define OPCODE_AUIPC        `OPCODE_LEN'b0010111
    `define OPCODE_BEQ          `OPCODE_LEN'b1100011
    `define OPCODE_BGE          `OPCODE_LEN'b1100011
    `define OPCODE_BGEU         `OPCODE_LEN'b1100011
    `define OPCODE_BLT          `OPCODE_LEN'b1100011
    `define OPCODE_BLTU         `OPCODE_LEN'b1100011
    `define OPCODE_BNE          `OPCODE_LEN'b1100011
    `define OPCODE_CSRRC        `OPCODE_LEN'b1110011
    `define OPCODE_CSRRCI       `OPCODE_LEN'b1110011
    `define OPCODE_CSRRS        `OPCODE_LEN'b1110011
    `define OPCODE_CSRRSI       `OPCODE_LEN'b1110011
    `define OPCODE_CSRRW        `OPCODE_LEN'b1110011
    `define OPCODE_CSRRWI       `OPCODE_LEN'b1110011
    `define OPCODE_EBREAK       `OPCODE_LEN'b1110011
    `define OPCODE_ECALL        `OPCODE_LEN'b1110011
    `define OPCODE_FENCE        `OPCODE_LEN'b0001111
    `define OPCODE_FENCE_I      `OPCODE_LEN'b0001111
    `define OPCODE_JAL          `OPCODE_LEN'b1101111
    `define OPCODE_JALR         `OPCODE_LEN'b1100111
    `define OPCODE_LB           `OPCODE_LEN'b0000011
    `define OPCODE_LBU          `OPCODE_LEN'b0000011
    `define OPCODE_LD           `OPCODE_LEN'b0000011
    `define OPCODE_LH           `OPCODE_LEN'b0000011
    `define OPCODE_LHU          `OPCODE_LEN'b0000011
    `define OPCODE_LW           `OPCODE_LEN'b0000011
    `define OPCODE_LWU          `OPCODE_LEN'b0000011
    `define OPCODE_LUI          `OPCODE_LEN'b0110111
    `define OPCODE_MRET         `OPCODE_LEN'b1110011
    `define OPCODE_OR           `OPCODE_LEN'b0110011
    `define OPCODE_ORI          `OPCODE_LEN'b0010011
    `define OPCODE_SB           `OPCODE_LEN'b0100011
    `define OPCODE_SD           `OPCODE_LEN'b0100011
    `define OPCODE_SFENCE_VMA   `OPCODE_LEN'b1110011
    `define OPCODE_SH           `OPCODE_LEN'b0100011
    `define OPCODE_SW           `OPCODE_LEN'b0100011
    `define OPCODE_SLL          `OPCODE_LEN'b0110011
    `define OPCODE_SLLI         `OPCODE_LEN'b0010011
    `define OPCODE_SLLIW        `OPCODE_LEN'b0011011
    `define OPCODE_SLLW         `OPCODE_LEN'b0111011
    `define OPCODE_SLT          `OPCODE_LEN'b0110011
    `define OPCODE_SLTI         `OPCODE_LEN'b0110011
    `define OPCODE_SLTIU        `OPCODE_LEN'b0010011
    `define OPCODE_SLTU         `OPCODE_LEN'b0110011
    `define OPCODE_SRA          `OPCODE_LEN'b0110011
    `define OPCODE_SRAI         `OPCODE_LEN'b0010011
    `define OPCODE_SRAIW        `OPCODE_LEN'b0011011
    `define OPCODE_SRAW         `OPCODE_LEN'b0111011
    `define OPCODE_SRET         `OPCODE_LEN'b1110011
    `define OPCODE_SRL          `OPCODE_LEN'b0110011
    `define OPCODE_SRLI         `OPCODE_LEN'b0010011
    `define OPCODE_SRLIW        `OPCODE_LEN'b0011011
    `define OPCODE_SRLW         `OPCODE_LEN'b0111011
    `define OPCODE_SUB          `OPCODE_LEN'b0110011
    `define OPCODE_SUBW         `OPCODE_LEN'b0111011
    `define OPCODE_WFI          `OPCODE_LEN'b1110011
    `define OPCODE_XOR          `OPCODE_LEN'b0110011
    `define OPCODE_XORI         `OPCODE_LEN'b0010011

    // FUNCT3: only R, I, S, SB type instructions
    // RV64I
    `define FUNCT3_ADD          `FUNCT3_LEN'b000
    `define FUNCT3_ADDI         `FUNCT3_LEN'b000
    `define FUNCT3_ADDIW        `FUNCT3_LEN'b000
    `define FUNCT3_ADDW         `FUNCT3_LEN'b000
    `define FUNCT3_AND          `FUNCT3_LEN'b111
    `define FUNCT3_ANDI         `FUNCT3_LEN'b111
    `define FUNCT3_BEQ          `FUNCT3_LEN'b000
    `define FUNCT3_BGE          `FUNCT3_LEN'b101
    `define FUNCT3_BGEU         `FUNCT3_LEN'b111
    `define FUNCT3_BLT          `FUNCT3_LEN'b100
    `define FUNCT3_BLTU         `FUNCT3_LEN'b110
    `define FUNCT3_BNE          `FUNCT3_LEN'b001
    `define FUNCT3_CSRRC        `FUNCT3_LEN'b011
    `define FUNCT3_CSRRCI       `FUNCT3_LEN'b111
    `define FUNCT3_CSRRS        `FUNCT3_LEN'b010
    `define FUNCT3_CSRRSI       `FUNCT3_LEN'b110
    `define FUNCT3_CSRRW        `FUNCT3_LEN'b001
    `define FUNCT3_CSRRWI       `FUNCT3_LEN'b101
    `define FUNCT3_EBREAK       `FUNCT3_LEN'b000
    `define FUNCT3_ECALL        `FUNCT3_LEN'b000
    `define FUNCT3_FENCE        `FUNCT3_LEN'b000
    `define FUNCT3_FENCE_I      `FUNCT3_LEN'b001
    `define FUNCT3_JALR         `FUNCT3_LEN'b000
    `define FUNCT3_LB           `FUNCT3_LEN'b000
    `define FUNCT3_LBU          `FUNCT3_LEN'b100
    `define FUNCT3_LD           `FUNCT3_LEN'b011
    `define FUNCT3_LH           `FUNCT3_LEN'b001
    `define FUNCT3_LHU          `FUNCT3_LEN'b101
    `define FUNCT3_LW           `FUNCT3_LEN'b010
    `define FUNCT3_LWU          `FUNCT3_LEN'b110
    `define FUNCT3_MRET         `FUNCT3_LEN'b000
    `define FUNCT3_OR           `FUNCT3_LEN'b110
    `define FUNCT3_ORI          `FUNCT3_LEN'b110
    `define FUNCT3_SB           `FUNCT3_LEN'b000
    `define FUNCT3_SD           `FUNCT3_LEN'b011
    `define FUNCT3_SFENCE_VMA   `FUNCT3_LEN'b000
    `define FUNCT3_SH           `FUNCT3_LEN'b001
    `define FUNCT3_SW           `FUNCT3_LEN'b010
    `define FUNCT3_SLL          `FUNCT3_LEN'b001
    `define FUNCT3_SLLI         `FUNCT3_LEN'b001
    `define FUNCT3_SLLIW        `FUNCT3_LEN'b001
    `define FUNCT3_SLLW         `FUNCT3_LEN'b001
    `define FUNCT3_SLT          `FUNCT3_LEN'b010
    `define FUNCT3_SLTI         `FUNCT3_LEN'b010
    `define FUNCT3_SLTIU        `FUNCT3_LEN'b011
    `define FUNCT3_SLTU         `FUNCT3_LEN'b011
    `define FUNCT3_SRA          `FUNCT3_LEN'b101
    `define FUNCT3_SRAI         `FUNCT3_LEN'b101
    `define FUNCT3_SRAIW        `FUNCT3_LEN'b101
    `define FUNCT3_SRAW         `FUNCT3_LEN'b101
    `define FUNCT3_SRET         `FUNCT3_LEN'b000
    `define FUNCT3_SRL          `FUNCT3_LEN'b101
    `define FUNCT3_SRLI         `FUNCT3_LEN'b101
    `define FUNCT3_SRLIW        `FUNCT3_LEN'b101
    `define FUNCT3_SRLW         `FUNCT3_LEN'b101
    `define FUNCT3_SUB          `FUNCT3_LEN'b000
    `define FUNCT3_SUBW         `FUNCT3_LEN'b000
    `define FUNCT3_WFI          `FUNCT3_LEN'b000
    `define FUNCT3_XOR          `FUNCT3_LEN'b100
    `define FUNCT3_XORI         `FUNCT3_LEN'b100

    // FUNCT7: only for R-type instructions
    // RV64I
    `define FUNCT7_ADD          `FUNCT7_LEN'b0000000
    `define FUNCT7_ADDW         `FUNCT7_LEN'b0000000
    `define FUNCT7_AND          `FUNCT7_LEN'b0000000
    `define FUNCT7_MRET         `FUNCT7_LEN'b0011000
    `define FUNCT7_OR           `FUNCT7_LEN'b0000000
    `define FUNCT7_SFENCE_VMA   `FUNCT7_LEN'b0001001
    `define FUNCT7_SLL          `FUNCT7_LEN'b0000000
    `define FUNCT7_SLLW         `FUNCT7_LEN'b0000000
    `define FUNCT7_SLT          `FUNCT7_LEN'b0000000
    `define FUNCT7_SLTU         `FUNCT7_LEN'b0000000
    `define FUNCT7_SRA          `FUNCT7_LEN'b0100000
    `define FUNCT7_SRAW         `FUNCT7_LEN'b0100000
    `define FUNCT7_SRET         `FUNCT7_LEN'b0001000
    `define FUNCT7_SRL          `FUNCT7_LEN'b0000000
    `define FUNCT7_SRLW         `FUNCT7_LEN'b0000000
    `define FUNCT7_SUB          `FUNCT7_LEN'b0100000
    `define FUNCT7_SUBW         `FUNCT7_LEN'b0100000
    `define FUNCT7_WFI          `FUNCT7_LEN'b0001000
    `define FUNCT7_XOR          `FUNCT7_LEN'b0000000

    //-------------------------\\
    //----- SPECIAL CODES -----\\
    //-------------------------\\
    
    // MRET
    `define MRET_RS2            5'b00010
    `define MRET_RS1            5'b00000
    `define MRET_RD             5'b00000

    // SRET
    `define SRET_RS2            `MRET_RS2
    `define SRET_RS1            `MRET_RS1
    `define SRET_RD             `MRET_RD

    // WFI
    `define WFI_RS2             5'b00101
    `define WFI_RS1             5'b00000
    `define WFI_RD              5'b00000

    // FENCE
    `define FENCE_RS1           5'b00000
    `define FENCE_RD            5'b00000
    `define FENCE_MSBS          4'b0000

    // FENCE.I
    `define FENCE_I_RS1         `FENCE_RS1
    `define FENCE_I_RD          `FENCE_RD
    `define FENCE_I_IMM         12'b000000000000

    // SFENCE.VMA
    `define SFENCE_VMA_RD       5'b00000

    // EBREAK
    `define EBREAK_RS1          5'b00000
    `define EBREAK_RD           5'b00000
    `define EBREAK_IMM          12'b000000000001

    // ECALL
    `define ECALL_RS1           5'b00000
    `define ECALL_RD            5'b00000
    `define ECALL_IMM           12'b000000000000

endpackage

`endif
