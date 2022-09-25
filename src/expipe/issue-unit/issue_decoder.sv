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
// File: decoder.sv
// Author: Michele Caon
// Date: 13/11/2019

// LEN5 compilation switches
`include "len5_config.svh"

// Import UVM report macros
`include "uvm_macros.svh"
import uvm_pkg::*;

/* Include instruction macros */
`include "instr_macros.svh"

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;

module issue_decoder (
    // Instruction from the issue logic
    input   instr_t         instruction_i,    // the issuing instruction
    
`ifdef LEN5_PRIVILEGED_EN
    // CSR data
    input                   mstatus_tsr_i,    // the TSR bit from the mstatus CSR
`endif /* LEN5_PRIVILEGED_EN */

    // Issue decoder <--> issue CU
    output  issue_type_t    issue_type_o,     // issue operation type

    // Information to the issue logic
    output  except_code_t   except_code_o,    // exception code to send to the ROB
    output  issue_eu_t      assigned_eu_o,    // assigned EU
    output  logic           skip_eu_o,        // do not assign to any EU
    output  eu_ctl_t        eu_ctl_o,         // controls for the assigned EU
    output  logic           rs1_req_o,        // rs1 fetch is required
    output  logic           rs1_is_pc_o,      // rs1 is the current PC (for AUIPC)
    output  logic           rs2_req_o,        // rs2 fetch is required
    output  logic           rs2_is_imm_o,     // replace rs2 value with imm. (for i-type ALU instr.)
`ifdef LEN5_FP_EN
    output  logic           rs3_req_o,        // rs3 (S, D only) fetch is required
`endif /* LEN5_FP_EN */
    output  logic           res_ready_o,      // the result is ready
    output  imm_format_t    imm_format_o      // immediate format
);

    // DEFINITIONS

    except_code_t                   except_code;
    issue_eu_t                      assigned_eu;
    eu_ctl_t                        eu_ctl;
    logic                           rs1_req; 
    logic                           rs1_is_pc;      // for AUIPC
    logic                           rs2_req;
    logic                           rs2_is_imm;     // for i-type ALU instr
`ifdef LEN5_FP_EN
    logic                           rs3_req;
`endif /* LEN5_FP_EN */
    imm_format_t                    imm_format;

    // ------------------
    // INSTRUCTION DECODE
    // ------------------
    // New supported instructions can be added here. The necessary defines must
    // be appended to the 'instr_macros.svh' file. 
    // The reporting order is the the one from Chapter 24 of the Specs.

    always_comb begin: instr_format_logic
        // DEFAULT VALUES 
        issue_type_o                = ISSUE_TYPE_NONE;
        except_code                 = E_UNKNOWN;
        skip_eu_o                   = 1'b0;
        assigned_eu                 = EU_INT_ALU;
        eu_ctl.raw                  = '0;
        rs1_req                     = 1'b0;
        rs1_is_pc                   = 1'b0;
        rs2_req                     = 1'b0;
        rs2_is_imm                  = 1'b0;
    `ifdef LEN5_FP_EN
        rs3_req                     = 1'b0;
    `endif /* LEN5_FP_EN */
        imm_format                  = IMM_TYPE_I;

        // ----------------
        // UNPRIVILEGED ISA
        // ----------------

        // NOP
        // NOTE: do not issue NOP to ALU
        if ((instruction_i.i.opcode == `OPCODE_ADDI) && 
            (instruction_i.i.funct3 == `FUNCT3_ADDI) && 
            ({instruction_i.i.imm11, instruction_i.i.rs1, instruction_i.i.rd} == '0)) begin
            skip_eu_o                   = 1'b1;
        end
        
        // RV64I
        // -----
        
        // LUI
        else if ((instruction_i.u.opcode == `OPCODE_LUI)) begin
            skip_eu_o                   = 1'b1;
            imm_format                  = IMM_TYPE_U;
            issue_type_o                = ISSUE_TYPE_LUI;
        end

        // AUIPC
        else if ((instruction_i.u.opcode == `OPCODE_AUIPC)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_ADD;
            imm_format                  = IMM_TYPE_U;
            rs1_is_pc                   = 1'b1;         // first operand is PC
            rs2_is_imm                  = 1'b1;         // second operand is U-immediate
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // JAL
        else if (instruction_i.j.opcode == `OPCODE_JAL) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl.bu                   = JAL;
            imm_format                  = IMM_TYPE_J;
            issue_type_o                = ISSUE_TYPE_JUMP;
        end 

        // JALR
        else if ((instruction_i.i.opcode == `OPCODE_JALR) && 
                (instruction_i.i.funct3 == `FUNCT3_JALR)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl.bu                   = JALR;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_JUMP;
        end

        // BEQ
        else if ((instruction_i.b.opcode == `OPCODE_BEQ) && 
                (instruction_i.b.funct3 == `FUNCT3_BEQ)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl.bu                   = BEQ;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
            issue_type_o                = ISSUE_TYPE_BRANCH;
        end

        // BNE
        else if ((instruction_i.b.opcode == `OPCODE_BNE) && 
                (instruction_i.b.funct3 == `FUNCT3_BNE)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl.bu                   = BNE;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
            issue_type_o                = ISSUE_TYPE_BRANCH;
        end

        // BLT
        else if ((instruction_i.b.opcode == `OPCODE_BLT) && 
                (instruction_i.b.funct3 == `FUNCT3_BLT)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl.bu                   = BLT;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
            issue_type_o                = ISSUE_TYPE_BRANCH;
        end

        // BGE
        else if ((instruction_i.b.opcode == `OPCODE_BGE) && 
                (instruction_i.b.funct3 == `FUNCT3_BGE)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl.bu                   = BGE;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
            issue_type_o                = ISSUE_TYPE_BRANCH;
        end

        // BLTU
        else if ((instruction_i.b.opcode == `OPCODE_BLTU) && 
                (instruction_i.b.funct3 == `FUNCT3_BLTU)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl.bu                   = BLTU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
            issue_type_o                = ISSUE_TYPE_BRANCH;
        end

        // BGEU
        else if ((instruction_i.b.opcode == `OPCODE_BGEU) && 
                (instruction_i.b.funct3 == `FUNCT3_BGEU)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl.bu                   = BGEU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
            issue_type_o                = ISSUE_TYPE_BRANCH;
        end

        // LB
        else if ((instruction_i.i.opcode == `OPCODE_LB) && 
                (instruction_i.i.funct3 == `FUNCT3_LB)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl.lsu                  = LS_BYTE;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // LH
        else if ((instruction_i.i.opcode == `OPCODE_LH) && 
                (instruction_i.i.funct3 == `FUNCT3_LH)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl.lsu                  = LS_HALFWORD;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // LW
        else if ((instruction_i.i.opcode == `OPCODE_LW) && 
                (instruction_i.i.funct3 == `FUNCT3_LW)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl.lsu                  = LS_WORD;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // LD
        else if ((instruction_i.i.opcode == `OPCODE_LD) && 
                (instruction_i.i.funct3 == `FUNCT3_LD)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl.lsu                  = LS_DOUBLEWORD;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // LBU
        else if ((instruction_i.i.opcode == `OPCODE_LBU) && 
                (instruction_i.i.funct3 == `FUNCT3_LBU)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl.lsu                  = LS_BYTE_U;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // LHU
        else if ((instruction_i.i.opcode == `OPCODE_LHU) && 
                (instruction_i.i.funct3 == `FUNCT3_LHU)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl.lsu                  = LS_HALFWORD_U;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // LWU
        else if ((instruction_i.i.opcode == `OPCODE_LWU) && 
                (instruction_i.i.funct3 == `FUNCT3_LWU)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl.lsu                  = LS_WORD_U;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SB
        else if ((instruction_i.s.opcode == `OPCODE_SB) && 
                (instruction_i.s.funct3 == `FUNCT3_SB)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            issue_type_o                = ISSUE_TYPE_STORE;
            eu_ctl.lsu                  = LS_BYTE;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_S;
        end

        // SH
        else if ((instruction_i.s.opcode == `OPCODE_SH) && 
                (instruction_i.s.funct3 == `FUNCT3_SH)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            issue_type_o                = ISSUE_TYPE_STORE;
            eu_ctl.lsu                  = LS_HALFWORD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_S;
        end

        // SW
        else if ((instruction_i.s.opcode == `OPCODE_SW) && 
                (instruction_i.s.funct3 == `FUNCT3_SW)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            issue_type_o                = ISSUE_TYPE_STORE;
            eu_ctl.lsu                  = LS_WORD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_S;
        end

        // SD
        else if ((instruction_i.s.opcode == `OPCODE_SD) && 
                (instruction_i.s.funct3 == `FUNCT3_SD)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            issue_type_o                = ISSUE_TYPE_STORE;
            eu_ctl.lsu                  = LS_DOUBLEWORD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_S;
        end

        // ADDI
        else if ((instruction_i.i.opcode == `OPCODE_ADDI) && 
                (instruction_i.i.funct3 == `FUNCT3_ADDI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_ADD;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // ADDIW
        else if ((instruction_i.i.opcode == `OPCODE_ADDIW) && 
                (instruction_i.i.funct3 == `FUNCT3_ADDIW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_ADDW;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SLTI
        else if ((instruction_i.i.opcode == `OPCODE_SLTI) && 
                (instruction_i.i.funct3 == `FUNCT3_SLTI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SLT;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end
        
        // SLTIU
        else if ((instruction_i.i.opcode == `OPCODE_SLTIU) && 
                (instruction_i.i.funct3 == `FUNCT3_SLTIU)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SLTU;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // XORI
        else if ((instruction_i.i.opcode == `OPCODE_XORI) && 
                (instruction_i.i.funct3 == `FUNCT3_XORI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_XOR;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // ORI
        else if ((instruction_i.i.opcode == `OPCODE_ORI) && 
                (instruction_i.i.funct3 == `FUNCT3_ORI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_OR;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // ANDI
        else if ((instruction_i.i.opcode == `OPCODE_ANDI) && 
                (instruction_i.i.funct3 == `FUNCT3_ANDI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_AND;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SLLIW
        else if ((instruction_i.i.opcode == `OPCODE_SLLIW) && 
                (instruction_i.i.funct3 == `FUNCT3_SLLIW) &&
                (instruction_i.i.imm11[31:25] == 7'b0000000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SLLW;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SLLI
        else if ((instruction_i.i.opcode == `OPCODE_SLLI) && 
                (instruction_i.i.funct3 == `FUNCT3_SLLI) &&
                (instruction_i.i.imm11[31:26] == 6'b000000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SLL;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SRLIW
        else if ((instruction_i.i.opcode == `OPCODE_SRLIW) && 
                (instruction_i.i.funct3 == `FUNCT3_SRLIW) &&
                (instruction_i.i.imm11[31:25] == 7'b0000000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SRLW;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SRLI
        else if ((instruction_i.i.opcode == `OPCODE_SRLI) && 
                (instruction_i.i.funct3 == `FUNCT3_SRLI) &&
                (instruction_i.i.imm11[31:26] == 6'b000000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SRL;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SRAIW
        else if ((instruction_i.i.opcode == `OPCODE_SRAIW) && 
                (instruction_i.i.funct3 == `FUNCT3_SRAIW) &&
                (instruction_i.i.imm11[31:25] == 7'b0100000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SRAW;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SRAI
        else if ((instruction_i.i.opcode == `OPCODE_SRAI) && 
                (instruction_i.i.funct3 == `FUNCT3_SRAI) &&
                (instruction_i.i.imm11[31:26] == 6'b010000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SRA;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // ADDW
        else if ((instruction_i.r.opcode == `OPCODE_ADDW) && 
                (instruction_i.r.funct3 == `FUNCT3_ADDW) && 
                (instruction_i.r.funct7 == `FUNCT7_ADDW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_ADDW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SUBW
        else if ((instruction_i.r.opcode == `OPCODE_SUBW) && 
                (instruction_i.r.funct3 == `FUNCT3_SUBW) && 
                (instruction_i.r.funct7 == `FUNCT7_SUBW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SUBW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // ADD
        else if ((instruction_i.r.opcode == `OPCODE_ADD) && 
            (instruction_i.r.funct3 == `FUNCT3_ADD) && 
            (instruction_i.r.funct7 == `FUNCT7_ADD)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_ADD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SUB
        else if ((instruction_i.r.opcode == `OPCODE_SUB) && 
                (instruction_i.r.funct3 == `FUNCT3_SUB) && 
                (instruction_i.r.funct7 == `FUNCT7_SUB)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SUB;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SLLW
        else if ((instruction_i.r.opcode == `OPCODE_SLLW) && 
                (instruction_i.r.funct3 == `FUNCT3_SLLW) && 
                (instruction_i.r.funct7 == `FUNCT7_SLLW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SLLW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SLL
        else if ((instruction_i.r.opcode == `OPCODE_SLL) && 
                (instruction_i.r.funct3 == `FUNCT3_SLL) && 
                (instruction_i.r.funct7 == `FUNCT7_SLL)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SLL;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SLT
        else if ((instruction_i.r.opcode == `OPCODE_SLT) && 
                (instruction_i.r.funct3 == `FUNCT3_SLT) && 
                (instruction_i.r.funct7 == `FUNCT7_SLT)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SLT;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SLTU
        else if ((instruction_i.r.opcode == `OPCODE_SLTU) && 
                (instruction_i.r.funct3 == `FUNCT3_SLTU) && 
                (instruction_i.r.funct7 == `FUNCT7_SLTU)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SLTU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // XOR
        else if ((instruction_i.r.opcode == `OPCODE_XOR) && 
                (instruction_i.r.funct3 == `FUNCT3_XOR) && 
                (instruction_i.r.funct7 == `FUNCT7_XOR)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_XOR;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SRLW
        else if ((instruction_i.r.opcode == `OPCODE_SRLW) && 
                (instruction_i.r.funct3 == `FUNCT3_SRLW) && 
                (instruction_i.r.funct7 == `FUNCT7_SRLW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SRLW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SRL
        else if ((instruction_i.r.opcode == `OPCODE_SRL) && 
                (instruction_i.r.funct3 == `FUNCT3_SRL) && 
                (instruction_i.r.funct7 == `FUNCT7_SRL)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SRL;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SRAW
        else if ((instruction_i.r.opcode == `OPCODE_SRAW) && 
                (instruction_i.r.funct3 == `FUNCT3_SRAW) && 
                (instruction_i.r.funct7 == `FUNCT7_SRAW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SRAW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // SRA
        else if ((instruction_i.r.opcode == `OPCODE_SRA) && 
                (instruction_i.r.funct3 == `FUNCT3_SRA) && 
                (instruction_i.r.funct7 == `FUNCT7_SRA)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_SRA;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // OR
        else if ((instruction_i.r.opcode == `OPCODE_OR) && 
                (instruction_i.r.funct3 == `FUNCT3_OR) && 
                (instruction_i.r.funct7 == `FUNCT7_OR)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_OR;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // AND
        else if ((instruction_i.r.opcode == `OPCODE_AND) && 
                (instruction_i.r.funct3 == `FUNCT3_AND) && 
                (instruction_i.r.funct7 == `FUNCT7_AND)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl.alu                  = ALU_AND;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end

        // FENCE
        else if ((instruction_i.i.opcode == `OPCODE_FENCE) && 
                (instruction_i.i.funct3 == `FUNCT3_FENCE) && 
                (instruction_i[30 -: 4] == `FENCE_FM_LSBS) && 
                (instruction_i.i.rs1 == `FENCE_RS1) && 
                (instruction_i.i.rd == `FENCE_RD)) begin
            issue_type_o                = ISSUE_TYPE_STALL;
            skip_eu_o                   = 1'b1;
        end

        // ECALL
        else if ((instruction_i.i.opcode == `OPCODE_ECALL) && 
                (instruction_i.i.funct3 == `FUNCT3_ECALL) && 
                (instruction_i.i.imm11 == `ECALL_IMM) && 
                (instruction_i.i.rs1 == `ECALL_RS1) && 
                (instruction_i.i.rd == `ECALL_RD)) begin
            issue_type_o                = ISSUE_TYPE_STALL;
            skip_eu_o                   = 1'b1;
        end

        // EBREAK
        else if ((instruction_i.i.opcode == `OPCODE_EBREAK) && 
                (instruction_i.i.funct3 == `FUNCT3_EBREAK) && 
                (instruction_i.i.imm11 == `EBREAK_IMM) && 
                (instruction_i.i.rs1 == `EBREAK_RS1) && 
                (instruction_i.i.rd == `EBREAK_RD)) begin
            skip_eu_o                   = 1'b1;
            issue_type_o                = ISSUE_TYPE_EXCEPT;
            except_code                 = E_BREAKPOINT;
        end

        // rv64 Zifencei
        // -------------

        // FENCE.I
        else if ((instruction_i.i.opcode == `OPCODE_FENCE_I) && 
                (instruction_i.i.funct3 == `FUNCT3_FENCE_I) && 
                (instruction_i.i.imm11 == `FENCE_I_IMM) && 
                (instruction_i.i.rs1 == `FENCE_I_RS1) && 
                (instruction_i.i.rd == `FENCE_I_RD)) begin
            issue_type_o                = ISSUE_TYPE_STALL;
            skip_eu_o                   = 1'b1;
        end

        // RV64 Zicsr
        // ----------

        // CSRRW
        else if ((instruction_i.i.opcode == `OPCODE_CSRRW) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRW)) begin
            skip_eu_o                   = 1'b1;
            rs1_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_CSR;
        end

        // CSRRS
        else if ((instruction_i.i.opcode == `OPCODE_CSRRS) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRS)) begin
            skip_eu_o                   = 1'b1;
            issue_type_o                = ISSUE_TYPE_CSR;
            rs1_req                     = 1'b1;
        end

        // CSRRC
        else if ((instruction_i.i.opcode == `OPCODE_CSRRC) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRC)) begin
            skip_eu_o                   = 1'b1;
            rs1_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_CSR;
        end

        // CSRRWI
        else if ((instruction_i.i.opcode == `OPCODE_CSRRWI) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRWI)) begin
            skip_eu_o                   = 1'b1;
            imm_format                  = IMM_TYPE_RS1;
            issue_type_o                = ISSUE_TYPE_CSR;
        end

        // CSRRSI
        else if ((instruction_i.i.opcode == `OPCODE_CSRRSI) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRSI)) begin
            skip_eu_o                   = 1'b1;
            imm_format                  = IMM_TYPE_RS1;
            issue_type_o                = ISSUE_TYPE_CSR;
        end

        // CSRRCI
        else if ((instruction_i.i.opcode == `OPCODE_CSRRCI) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRCI)) begin
            skip_eu_o                   = 1'b1;
            imm_format                  = IMM_TYPE_RS1;
            issue_type_o                = ISSUE_TYPE_CSR;
        end

    `ifdef LEN5_M_EN

        // RV64M
        // -----
        // NOTE: DIV and REM to be implemented

        // MUL
        else if ((instruction_i.r.opcode == `OPCODE_MUL) &&
                (instruction_i.r.funct3 == `FUNCT3_MUL) &&
                (instruction_i.r.funct7 == `FUNCT7_MUL)) begin
            assigned_eu                 = EU_INT_MULT;
            eu_ctl.mult                 = MULT_MUL;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end
        
        // MULW
        else if ((instruction_i.r.opcode == `OPCODE_MULW) &&
                (instruction_i.r.funct3 == `FUNCT3_MULW) &&
                (instruction_i.r.funct7 == `FUNCT7_MULW)) begin
            assigned_eu                 = EU_INT_MULT;
            eu_ctl.mult                 = MULT_MULW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_INT;
        end
        
        // MULH
        else if ((instruction_i.r.opcode == `OPCODE_MULH) &&
                (instruction_i.r.funct3 == `FUNCT3_MULH) &&
                (instruction_i.r.funct7 == `FUNCT7_MULH)) begin
            assigned_eu                 = EU_INT_MULT;
            eu_ctl.mult                 = MULT_MULH;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_CSR;
        end
        
        // MULHSU
        else if ((instruction_i.r.opcode == `OPCODE_MULHSU) &&
                (instruction_i.r.funct3 == `FUNCT3_MULHSU) &&
                (instruction_i.r.funct7 == `FUNCT7_MULHSU)) begin
            assigned_eu                 = EU_INT_MULT;
            eu_ctl.mult                 = MULT_MULHSU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_CSR;
        end
        
        // MULHU
        else if ((instruction_i.r.opcode == `OPCODE_MULHU) &&
                (instruction_i.r.funct3 == `FUNCT3_MULHU) &&
                (instruction_i.r.funct7 == `FUNCT7_MULHU)) begin
            assigned_eu                 = EU_INT_MULT;
            eu_ctl.mult                 = MULT_MULHU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            issue_type_o                = ISSUE_TYPE_CSR;
        end

    `endif /* LEN5_M_EN */

        // RV64A
        // -----
        // NOTE: to be implemented for OS support

    `ifdef LEN5_FP_EN

        // RV64F
        // -----

        // RV64D
        // -----

    `endif /* LEN5_FP_EN */

    `ifdef LEN5_PRIVILEGED_EN

        // --------------
        // PRIVILEGED ISA
        // --------------

        // Trap-Return Instructions
        // ------------------------

        // URET
        else if ((instruction_i.r.opcode == `OPCODE_URET) && 
                (instruction_i.r.funct3 == `FUNCT3_URET) && 
                (instruction_i.r.funct7 == `FUNCT7_URET) && 
                (instruction_i.r.rs2 == `URET_RS2) && 
                (instruction_i.r.rs1 == `URET_RS1) && 
                (instruction_i.r.rd == `URET_RD)) begin
            issue_type_o                = ISSUE_TYPE_STALL;
            skip_eu_o                   = 1'b1;
        end

        // SRET
        else if ((instruction_i.r.opcode == `OPCODE_SRET) && 
                (instruction_i.r.funct3 == `FUNCT3_SRET) && 
                (instruction_i.r.funct7 == `FUNCT7_SRET) && 
                (instruction_i.r.rs2 == `SRET_RS2) && 
                (instruction_i.r.rs1 == `SRET_RS1) && 
                (instruction_i.r.rd == `SRET_RD)) begin
            if (mstatus_tsr_i) begin
                issue_type_o            = ISSUE_TYPE_EXCEPT;
                except_code_t           = E_ILLEGAL_INSTRUCTION;
            end else begin
                issue_type_o            = ISSUE_TYPE_STALL;
            end
        end

        // MRET
        else if ((instruction_i.r.opcode == `OPCODE_MRET) && 
                (instruction_i.r.funct3 == `FUNCT3_MRET) && 
                (instruction_i.r.funct7 == `FUNCT7_MRET) && 
                (instruction_i.r.rs2 == `MRET_RS2) && 
                (instruction_i.r.rs1 == `MRET_RS1) && 
                (instruction_i.r.rd == `MRET_RD)) begin
            skip_eu_o                   = 1'b1;
            issue_type_o                = ISSUE_TYPE_STALL;
        end

        // Interrupt-Management Instructions
        // ---------------------------------

        // WFI
        else if ((instruction_i.r.opcode == `OPCODE_WFI) && 
                (instruction_i.r.funct3 == `FUNCT3_WFI) && 
                (instruction_i.r.funct7 == `FUNCT7_WFI) && 
                (instruction_i.r.rs2 == `WFI_RS2) && 
                (instruction_i.r.rs1 == `WFI_RS1) && 
                (instruction_i.r.rd == `WFI_RD)) begin
            skip_eu_o                   = 1'b1;
            issue_type_o                = ISSUE_TYPE_WFI;
        end

        // Supervisor Memory-Management Instructions
        // -----------------------------------------

        // SFENCE.VMA
        else if ((instruction_i.r.opcode == `OPCODE_SFENCE_VMA) && 
                (instruction_i.r.funct3 == `FUNCT3_SFENCE_VMA) && 
                (instruction_i.r.funct7 == `FUNCT7_SFENCE_VMA) && 
                (instruction_i.r.rd == `SFENCE_VMA_RD)) begin
            skip_eu_o                   = 1'b1;
            issue_type_o                = ISSUE_TYPE_STALL;
        end

        // Hypervisor Memory-Management Instructions
        // -----------------------------------------

        // HFENCE.BVMA
        else if ((instruction_i.r.opcode == `OPCODE_HFENCE_BVMA) && 
                (instruction_i.r.funct3 == `FUNCT3_HFENCE_BVMA) && 
                (instruction_i.r.funct7 == `FUNCT7_HFENCE_BVMA) && 
                (instruction_i.r.rd == `HFENCE_BVMA_RD)) begin
            skip_eu_o                   = 1'b1;
            issue_type_o                = ISSUE_TYPE_STALL;
        end

        // HFENCE.GVMA
        else if ((instruction_i.r.opcode == `OPCODE_HFENCE_GVMA) && 
                (instruction_i.r.funct3 == `FUNCT3_HFENCE_GVMA) && 
                (instruction_i.r.funct7 == `FUNCT7_HFENCE_GVMA) && 
                (instruction_i.r.rd == `HFENCE_GVMA_RD)) begin
            skip_eu_o                   = 1'b1;
            issue_type_o                = ISSUE_TYPE_STALL;
        end

    `endif /* LEN5_PRIVILEGED_EN */
        
        // UNSUPPORTED INSTRUCTION
        // -----------------------

        else begin
            skip_eu_o                   = 1'b1;
            issue_type_o                = ISSUE_TYPE_EXCEPT;
            except_code                 = E_ILLEGAL_INSTRUCTION;
        end
    end

    // -----------------
    // OUTPUT GENERATION
    // -----------------
    assign except_code_o        = except_code;
    assign assigned_eu_o        = assigned_eu;
    assign eu_ctl_o             = eu_ctl;
    assign rs1_req_o            = rs1_req;
    assign rs1_is_pc_o          = rs1_is_pc;
    assign rs2_req_o            = rs2_req;
    assign rs2_is_imm_o         = rs2_is_imm;
`ifdef LEN5_FP_EN
    assign rs3_req_o            = rs3_req;
`endif /* LEN5_FP_EN */
    assign imm_format_o         = imm_format;

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    /* Assertions here */
    `endif
    
endmodule
