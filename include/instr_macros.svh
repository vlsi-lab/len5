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
// File: instr_macros.svh
// Author: Michele Caon
// Date: 12/11/2019

`ifndef INSTR_MACROS_
`define INSTR_MACROS_

import len5_pkg::XLEN;

//-----------------------------\\
//----- INSTRUCTION CODES -----\\
//-----------------------------\\

// OPCODE: all instructions 
// RV64I
`define OPCODE_ADD          7'b0110011
`define OPCODE_ADDI         7'b0010011
`define OPCODE_ADDIW        7'b0011011
`define OPCODE_ADDW         7'b0111011
`define OPCODE_AND          7'b0110011
`define OPCODE_ANDI         7'b0010011
`define OPCODE_AUIPC        7'b0010111
`define OPCODE_BEQ          7'b1100011
`define OPCODE_BGE          7'b1100011
`define OPCODE_BGEU         7'b1100011
`define OPCODE_BLT          7'b1100011
`define OPCODE_BLTU         7'b1100011
`define OPCODE_BNE          7'b1100011
`define OPCODE_CSRRC        7'b1110011
`define OPCODE_CSRRCI       7'b1110011
`define OPCODE_CSRRS        7'b1110011
`define OPCODE_CSRRSI       7'b1110011
`define OPCODE_CSRRW        7'b1110011
`define OPCODE_CSRRWI       7'b1110011
`define OPCODE_EBREAK       7'b1110011
`define OPCODE_ECALL        7'b1110011
`define OPCODE_FENCE        7'b0001111
`define OPCODE_FENCE_I      7'b0001111
`define OPCODE_JAL          7'b1101111
`define OPCODE_JALR         7'b1100111
`define OPCODE_LB           7'b0000011
`define OPCODE_LBU          7'b0000011
`define OPCODE_LD           7'b0000011
`define OPCODE_LH           7'b0000011
`define OPCODE_LHU          7'b0000011
`define OPCODE_LW           7'b0000011
`define OPCODE_LWU          7'b0000011
`define OPCODE_LUI          7'b0110111
`define OPCODE_MRET         7'b1110011
`define OPCODE_OR           7'b0110011
`define OPCODE_ORI          7'b0010011
`define OPCODE_SB           7'b0100011
`define OPCODE_SD           7'b0100011
`define OPCODE_SFENCE_VMA   7'b1110011
`define OPCODE_SH           7'b0100011
`define OPCODE_SW           7'b0100011
`define OPCODE_SLL          7'b0110011
`define OPCODE_SLLI         7'b0010011
`define OPCODE_SLLIW        7'b0011011
`define OPCODE_SLLW         7'b0111011
`define OPCODE_SLT          7'b0110011
`define OPCODE_SLTI         7'b0110011
`define OPCODE_SLTIU        7'b0010011
`define OPCODE_SLTU         7'b0110011
`define OPCODE_SRA          7'b0110011
`define OPCODE_SRAI         7'b0010011
`define OPCODE_SRAIW        7'b0011011
`define OPCODE_SRAW         7'b0111011
`define OPCODE_SRET         7'b1110011
`define OPCODE_SRL          7'b0110011
`define OPCODE_SRLI         7'b0010011
`define OPCODE_SRLIW        7'b0011011
`define OPCODE_SRLW         7'b0111011
`define OPCODE_SUB          7'b0110011
`define OPCODE_SUBW         7'b0111011
`define OPCODE_WFI          7'b1110011
`define OPCODE_XOR          7'b0110011
`define OPCODE_XORI         7'b0010011

// FUNCT3: only R, I, S, SB type instructions
// RV64I
`define FUNCT3_ADD          3'b000
`define FUNCT3_ADDI         3'b000
`define FUNCT3_ADDIW        3'b000
`define FUNCT3_ADDW         3'b000
`define FUNCT3_AND          3'b111
`define FUNCT3_ANDI         3'b111
`define FUNCT3_BEQ          3'b000
`define FUNCT3_BGE          3'b101
`define FUNCT3_BGEU         3'b111
`define FUNCT3_BLT          3'b100
`define FUNCT3_BLTU         3'b110
`define FUNCT3_BNE          3'b001
`define FUNCT3_CSRRC        3'b011
`define FUNCT3_CSRRCI       3'b111
`define FUNCT3_CSRRS        3'b010
`define FUNCT3_CSRRSI       3'b110
`define FUNCT3_CSRRW        3'b001
`define FUNCT3_CSRRWI       3'b101
`define FUNCT3_EBREAK       3'b000
`define FUNCT3_ECALL        3'b000
`define FUNCT3_FENCE        3'b000
`define FUNCT3_FENCE_I      3'b001
`define FUNCT3_JALR         3'b000
`define FUNCT3_LB           3'b000
`define FUNCT3_LBU          3'b100
`define FUNCT3_LD           3'b011
`define FUNCT3_LH           3'b001
`define FUNCT3_LHU          3'b101
`define FUNCT3_LW           3'b010
`define FUNCT3_LWU          3'b110
`define FUNCT3_MRET         3'b000
`define FUNCT3_OR           3'b110
`define FUNCT3_ORI          3'b110
`define FUNCT3_SB           3'b000
`define FUNCT3_SD           3'b011
`define FUNCT3_SFENCE_VMA   3'b000
`define FUNCT3_SH           3'b001
`define FUNCT3_SW           3'b010
`define FUNCT3_SLL          3'b001
`define FUNCT3_SLLI         3'b001
`define FUNCT3_SLLIW        3'b001
`define FUNCT3_SLLW         3'b001
`define FUNCT3_SLT          3'b010
`define FUNCT3_SLTI         3'b010
`define FUNCT3_SLTIU        3'b011
`define FUNCT3_SLTU         3'b011
`define FUNCT3_SRA          3'b101
`define FUNCT3_SRAI         3'b101
`define FUNCT3_SRAIW        3'b101
`define FUNCT3_SRAW         3'b101
`define FUNCT3_SRET         3'b000
`define FUNCT3_SRL          3'b101
`define FUNCT3_SRLI         3'b101
`define FUNCT3_SRLIW        3'b101
`define FUNCT3_SRLW         3'b101
`define FUNCT3_SUB          3'b000
`define FUNCT3_SUBW         3'b000
`define FUNCT3_WFI          3'b000
`define FUNCT3_XOR          3'b100
`define FUNCT3_XORI         3'b100

// FUNCT7: only for R-type instructions
// RV64I
`define FUNCT7_ADD          7'b0000000
`define FUNCT7_ADDW         7'b0000000
`define FUNCT7_AND          7'b0000000
`define FUNCT7_MRET         7'b0011000
`define FUNCT7_OR           7'b0000000
`define FUNCT7_SFENCE_VMA   7'b0001001
`define FUNCT7_SLL          7'b0000000
`define FUNCT7_SLLW         7'b0000000
`define FUNCT7_SLT          7'b0000000
`define FUNCT7_SLTU         7'b0000000
`define FUNCT7_SRA          7'b0100000
`define FUNCT7_SRAW         7'b0100000
`define FUNCT7_SRET         7'b0001000
`define FUNCT7_SRL          7'b0000000
`define FUNCT7_SRLW         7'b0000000
`define FUNCT7_SUB          7'b0100000
`define FUNCT7_SUBW         7'b0100000
`define FUNCT7_WFI          7'b0001000
`define FUNCT7_XOR          7'b0000000

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

`endif /* INSTR_MACROS_ */

