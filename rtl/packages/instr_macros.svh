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

// -----------------
// INSTRUCTION CODES
// -----------------

// OPCODE
`define OPCODE_OP_IMM 7'b0010011
`define OPCODE_OP_IMM_32 7'b0011011
`define OPCODE_OP 7'b0110011
`define OPCODE_OP_32 7'b0111011
`define OPCODE_LUI 7'b0110111
`define OPCODE_AUIPC 7'b0010111
`define OPCODE_JAL 7'b1101111
`define OPCODE_JALR 7'b1100111
`define OPCODE_BRANCH 7'b1100011
`define OPCODE_LOAD 7'b0000011
`define OPCODE_STORE 7'b0100011
`define OPCODE_SYSTEM 7'b1110011
`define OPCODE_MISC_MEM 7'b0001111
`define OPCODE_AMO 7'b0101111
`define OPCODE_LOAD_FP 7'b0000111
`define OPCODE_STORE_FP 7'b0100111
`define OPCODE_OP_FP 7'b1010011
`define OPCODE_FMADD 7'b1000011
`define OPCODE_FNMADD 7'b1001111
`define OPCODE_FMSUB 7'b1000111
`define OPCODE_FNMSUB 7'b1001011

// FUNCT3: only R, I, S, SB type instructions
// ALU
`define FUNCT3_ADD 3'b000
`define FUNCT3_ADDI `FUNCT3_ADD
`define FUNCT3_ADDW `FUNCT3_ADD
`define FUNCT3_ADDIW `FUNCT3_ADD
`define FUNCT3_SUB `FUNCT3_ADD
`define FUNCT3_SUBW `FUNCT3_ADD
`define FUNCT3_SLL 3'b001
`define FUNCT3_SLLI `FUNCT3_SLL
`define FUNCT3_SLLIW `FUNCT3_SLL
`define FUNCT3_SLLW `FUNCT3_SLL
`define FUNCT3_SLT 3'b010
`define FUNCT3_SLTI `FUNCT3_SLT
`define FUNCT3_SLTU 3'b011
`define FUNCT3_SLTIU `FUNCT3_SLTU
`define FUNCT3_XOR 3'b100
`define FUNCT3_XORI `FUNCT3_XOR
`define FUNCT3_SRA 3'b101
`define FUNCT3_SRAI `FUNCT3_SRA
`define FUNCT3_SRAIW `FUNCT3_SRA
`define FUNCT3_SRAW `FUNCT3_SRA
`define FUNCT3_SRL `FUNCT3_SRA
`define FUNCT3_SRLI `FUNCT3_SRA
`define FUNCT3_SRLIW `FUNCT3_SRA
`define FUNCT3_SRLW `FUNCT3_SRA
`define FUNCT3_OR 3'b110
`define FUNCT3_ORI `FUNCT3_OR
`define FUNCT3_AND 3'b111
`define FUNCT3_ANDI `FUNCT3_AND
// JUMP
`define FUNCT3_JALR 3'b000
// BRANCH
`define FUNCT3_BEQ 3'b000
`define FUNCT3_BNE 3'b001
`define FUNCT3_BLT 3'b100
`define FUNCT3_BGE 3'b101
`define FUNCT3_BLTU 3'b110
`define FUNCT3_BGEU 3'b111
// LOAD/STORE
`define FUNCT3_LB 3'b000
`define FUNCT3_LBU 3'b100
`define FUNCT3_LH 3'b001
`define FUNCT3_LHU 3'b101
`define FUNCT3_LW 3'b010
`define FUNCT3_LWU 3'b110
`define FUNCT3_LD 3'b011
`define FUNCT3_SB 3'b000
`define FUNCT3_SH 3'b001
`define FUNCT3_SW 3'b010
`define FUNCT3_SD 3'b011
// CSR
`define FUNCT3_CSRRW 3'b001
`define FUNCT3_CSRRS 3'b010
`define FUNCT3_CSRRC 3'b011
`define FUNCT3_CSRRWI 3'b101
`define FUNCT3_CSRRSI 3'b110
`define FUNCT3_CSRRCI 3'b111
// SYSTEM
`define FUNCT3_ZERO 3'b000
`define FUNCT3_EBREAK `FUNCT3_ZERO
`define FUNCT3_ECALL `FUNCT3_ZERO
`define FUNCT3_FENCE `FUNCT3_ZERO
`define FUNCT3_HFENCE_BVMA `FUNCT3_ZERO
`define FUNCT3_HFENCE_GVMA `FUNCT3_ZERO
`define FUNCT3_MRET `FUNCT3_ZERO
`define FUNCT3_SFENCE_VMA `FUNCT3_ZERO
`define FUNCT3_SRET `FUNCT3_ZERO
`define FUNCT3_URET `FUNCT3_ZERO
`define FUNCT3_WFI `FUNCT3_ZERO
`define FUNCT3_FENCE_I 3'b001
// MULT/DIV
`define FUNCT3_MUL 3'b000
`define FUNCT3_MULW `FUNCT3_MUL
`define FUNCT3_MULH 3'b001
`define FUNCT3_MULHSU 3'b010
`define FUNCT3_MULHU 3'b011
`define FUNCT3_DIV 3'b100
`define FUNCT3_DIVW `FUNCT3_DIV
`define FUNCT3_DIVU 3'b101
`define FUNCT3_DIVUW `FUNCT3_DIVU
`define FUNCT3_REM 3'b110
`define FUNCT3_REMW `FUNCT3_REM
`define FUNCT3_REMU 3'b111
`define FUNCT3_REMUW `FUNCT3_REMU

// RV64F
`define FUNCT3_FLW 3'b010
`define FUNCT3_FSW 3'b010
`define FUNCT3_FSGNJ_S 3'b000
`define FUNCT3_FSGNJN_S 3'b001
`define FUNCT3_FSGNJX_S 3'b010
`define FUNCT3_FMIN_S 3'b000
`define FUNCT3_FMAX_S 3'b001
`define FUNCT3_FMV_X_W 3'b000
`define FUNCT3_FEQ_S 3'b010
`define FUNCT3_FLT_S 3'b001
`define FUNCT3_FLE_S 3'b000
`define FUNCT3_FCLASS_S 3'b001
`define FUNCT3_FMV_W_X 3'b000

// FUNCT7: only for R-type instructions
`define FUNCT7_ZERO 7'b0000000
`define FUNCT7_OP 7'b0000000
`define FUNCT7_OP_ALT 7'b0100000
`define FUNCT7_ADD `FUNCT7_OP
`define FUNCT7_ADDW `FUNCT7_OP
`define FUNCT7_AND `FUNCT7_OP
`define FUNCT7_HFENCE_BVMA 7'b0010001
`define FUNCT7_HFENCE_GVMA 7'b1010001
`define FUNCT7_MRET 7'b0011000
`define FUNCT7_OR `FUNCT7_OP
`define FUNCT7_SFENCE_VMA 7'b0001001
`define FUNCT7_SLL `FUNCT7_OP
`define FUNCT7_SLLW `FUNCT7_OP
`define FUNCT7_SLT `FUNCT7_OP
`define FUNCT7_SLTU `FUNCT7_OP
`define FUNCT7_SRA `FUNCT7_OP_ALT
`define FUNCT7_SRAW `FUNCT7_OP_ALT
`define FUNCT7_SRET 7'b0001000
`define FUNCT7_SRL `FUNCT7_OP
`define FUNCT7_SRLW `FUNCT7_OP
`define FUNCT7_SUB `FUNCT7_OP_ALT
`define FUNCT7_SUBW `FUNCT7_OP_ALT
`define FUNCT7_URET 7'b0011000
`define FUNCT7_WFI 7'b0001000
`define FUNCT7_XOR `FUNCT7_OP

// RV64M
`define FUNCT7_M 7'b0000001

// RV64F
`define FUNCT7_FADD_S 7'b0000000
`define FUNCT7_FSUB_S 7'b0000100
`define FUNCT7_FMUL_S 7'b0001000
`define FUNCT7_FDIV_S 7'b0001100
`define FUNCT7_FSQRT_S 7'b0101100
`define FUNCT7_FSGNJ_S 7'b0010000
`define FUNCT7_FSGNJN_S 7'b0010000
`define FUNCT7_FSGNJX_S 7'b0010000
`define FUNCT7_FMIN_S 7'b0010100
`define FUNCT7_FMAX_S 7'b0010100
`define FUNCT7_FCVT_W_S 7'b1100000
`define FUNCT7_FCVT_WU_S 7'b1100000
`define FUNCT7_FMV_X_W 7'b1110000
`define FUNCT7_FEQ_S 7'b1010000
`define FUNCT7_FLT_S 7'b1010000
`define FUNCT7_FLE_S 7'b1010000
`define FUNCT7_FCLASS_S 7'b1110000
`define FUNCT7_FCVT_S_W 7'b1101000
`define FUNCT7_FCVT_S_WU 7'b1101000
`define FUNCT7_FMV_W_X 7'b1111000
`define FUNCT7_FCVT_L_S 7'b1100000
`define FUNCT7_FCVT_LU_S 7'b1100000
`define FUNCT7_FCVT_S_L 7'b1101000
`define FUNCT7_FCVT_S_LU 7'b1101000

// FUNCT2: only for R4-type insrtructions
`define FUNCT2_FMADD_S 2'b00
`define FUNCT2_FMSUB_S 2'b00
`define FUNCT2_FNMSUB_S 2'b00
`define FUNCT2_FNMADD_S 2'b00

//-------------------
// SPECIAL CODES
//-------------------

// URET
`define URET_RS2 5'b00010
`define URET_RS1 5'b00000
`define URET_RD 5'b00000

// MRET
`define MRET_RS2 `URET_RS2
`define MRET_RS1 `URET_RS1
`define MRET_RD `URET_RD

// SRET
`define SRET_RS2 `MRET_RS2
`define SRET_RS1 `MRET_RS1
`define SRET_RD `MRET_RD

// WFI
`define WFI_RS2 5'b00101
`define WFI_RS1 5'b00000
`define WFI_RD 5'b00000

// FENCE
`define FENCE_RS1 5'b00000
`define FENCE_RD 5'b00000
`define FENCE_FM_LSBS 3'b000

// FENCE.I
`define FENCE_I_RS1 `FENCE_RS1
`define FENCE_I_RD `FENCE_RD
`define FENCE_I_IMM 12'b000000000000

// SFENCE.VMA
`define SFENCE_VMA_RD 5'b00000

// HFENCE.BVMA
`define HFENCE_BVMA_RD 5'b00000

// HFENCE.GVMA
`define HFENCE_GVMA_RD 5'b00000

// EBREAK
`define EBREAK_RS1 5'b00000
`define EBREAK_RD 5'b00000
`define EBREAK_IMM 12'b000000000001

// ECALL
`define ECALL_RS1 5'b00000
`define ECALL_RD 5'b00000
`define ECALL_IMM 12'b000000000000

// RV64F
`define FSQRT_S_RS2 5'b00000
`define FCVT_W_S_RS2 5'b00000
`define FCVT_WU_S_RS2 5'b00001
`define FMV_X_W_RS2 5'b00000
`define FCLASS_S_RS2 5'b00000
`define FCVT_S_W_RS2 5'b00000
`define FCVT_S_WU_RS2 5'b00001
`define FCVT_L_S_RS2 5'b00010
`define FCVT_LU_S_RS2 5'b00011
`define FCVT_S_L_RS2 5'b00010
`define FCVT_S_LU_RS2 5'b00011

// COMPRESSED INSTRUCTIONS
// opcode (1:0)
`define C_OP_C0 2'b00
`define C_OP_C1 2'b01
`define C_OP_C2 2'b10
// funct3 (15:13)


`endif  /* INSTR_MACROS_ */

