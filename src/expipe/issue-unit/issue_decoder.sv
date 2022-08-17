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
    input   instr_t                         instruction_i,    // the issuing instruction
    
`ifdef LEN5_PRIVILEGED_EN
    // CSR data
    input                                   mstatus_tsr_i,    // the TSR bit from the mstatus CSR
`endif /* LEN5_PRIVILEGED_EN */

    // Information to the issue logic
    output  logic                           except_raised_o,  // an exception occurred during decoding
    output  except_code_t                   except_code_o,    // exception code to send to the ROB
    output  logic                           res_ready_o,      // force ready to commit in the ROB
    output  logic                           stall_possible_o, // the instruction issue can be stall to save power

    output  issue_eu_t                      eu_o,             // assigned EU
    output  logic [MAX_EU_CTL_LEN-1:0]      eu_ctl_o,         // controls for the assigned EU
    output  logic                           fp_rs_o,          // source operands are from FP register file
    output  logic                           rs1_req_o,        // rs1 fetch is required
    output  logic                           rs1_is_pc_o,      // rs1 is the current PC (for AUIPC)
    output  logic                           rs2_req_o,        // rs2 fetch is required
    output  logic                           rs2_is_imm_o,     // replace rs2 value with imm. (for i-type ALU instr.)
`ifdef LEN5_FP_EN
    output  logic                           rs3_req_o,        // rs3 (S, D only) fetch is required
`endif /* LEN5_FP_EN */
    output  imm_format_t                    imm_format_o,     // immediate format    
    output  logic                           regstat_upd_o     // the register status must be updated
);

    // DEFINITIONS

    logic                           except_raised; 
    except_code_t                   except_code;
    logic                           res_ready;
    logic                           stall_possible;
    issue_eu_t                      assigned_eu;
    logic [MAX_EU_CTL_LEN-1:0]      eu_ctl;
    logic                           rs_fp;
    logic                           rs1_req; 
    logic                           rs1_is_pc;      // for AUIPC
    logic                           rs2_req;
    logic                           rs2_is_imm;     // for i-type ALU instr
`ifdef LEN5_FP_EN
    logic                           rs3_req;
`endif /* LEN5_FP_EN */
    imm_format_t                    imm_format;
    logic                           regstat_upd;

    // ------------------
    // INSTRUCTION DECODE
    // ------------------
    // New supported instructions can be added here. The necessary defines must
    // be appended to the 'instr_macros.svh' file. 
    // The reporting order is the the one from Chapter 24 of the Specs.

    always_comb begin: instr_format_logic
        // DEFAULT VALUES 
        except_raised               = 1'b0; 
        except_code                 = E_UNKNOWN;    // whatever: ignored if except_raised is not asserted
        res_ready                   = 1'b0;
        stall_possible              = 1'b0;
        assigned_eu                 = EU_NONE;       // whatever: ignored if except_raised is asserted
        eu_ctl                      = 0;
        rs_fp                       = 1'b0;         // normally from the integer register file
        rs1_req                     = 1'b0;
        rs1_is_pc                   = 1'b0;
        rs2_req                     = 1'b0;
        rs2_is_imm                  = 1'b0;
    `ifdef LEN5_FP_EN
        rs3_req                     = 1'b0;
    `endif /* LEN5_FP_EN */
        imm_format                  = IMM_TYPE_I;
        regstat_upd                 = 1'b0;

        // ----------------
        // UNPRIVILEGED ISA
        // ----------------

        // NOP
        // NOTE: do not issue NOP to ALU
        if ((instruction_i.i.opcode == `OPCODE_ADDI) && 
            (instruction_i.i.funct3 == `FUNCT3_ADDI) && 
            (instruction_i.i.rs1 == '0) && 
            (instruction_i.i.imm11 == '0)) begin
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            stall_possible              = 1'b1;
        end
        
        // RV64I
        // -----
        
        // LUI
        else if ((instruction_i.u.opcode == `OPCODE_LUI)) begin
            assigned_eu                 = EU_NONE;
            imm_format                  = IMM_TYPE_U;
            res_ready                   = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // AUIPC
        else if ((instruction_i.u.opcode == `OPCODE_AUIPC)) begin
            // depending on how it's implemented, stalling the fetch and issue could be convenient or not
            // stall_possible              = 1'b1;
            assigned_eu                 = EU_INT_ALU;
            eu_ctl                      = ALU_ADD;
            imm_format                  = IMM_TYPE_U;
            rs1_is_pc                   = 1'b1;         // first operand is PC
            rs2_is_imm                  = 1'b1;         // second operand is U-immediate
            regstat_upd                 = 1'b1;
        end

        // JAL
        else if (instruction_i.j.opcode == `OPCODE_JAL) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl                      = JUMP;
            imm_format                  = IMM_TYPE_J;
            rs1_is_pc                   = 1'b1;         // first operand is pc
            rs2_is_imm                  = 1'b1;         // second operand is J-immediate
            regstat_upd                 = 1'b1;
            stall_possible              = 1'b1;
        end 

        // JALR
        else if ((instruction_i.i.opcode == `OPCODE_JALR) && 
                (instruction_i.i.funct3 == `FUNCT3_JALR)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl                      = ALU_ADD;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;         // second operand is I-immediate
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
            stall_possible              = 1'b1;
        end

        // BEQ
        else if ((instruction_i.b.opcode == `OPCODE_BEQ) && 
                (instruction_i.b.funct3 == `FUNCT3_BEQ)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BEQ;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
        end

        // BNE
        else if ((instruction_i.b.opcode == `OPCODE_BNE) && 
                (instruction_i.b.funct3 == `FUNCT3_BNE)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BNE;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
        end

        // BLT
        else if ((instruction_i.b.opcode == `OPCODE_BLT) && 
                (instruction_i.b.funct3 == `FUNCT3_BLT)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BLT;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
        end

        // BGE
        else if ((instruction_i.b.opcode == `OPCODE_BGE) && 
                (instruction_i.b.funct3 == `FUNCT3_BGE)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BGE;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
        end

        // BLTU
        else if ((instruction_i.b.opcode == `OPCODE_BLTU) && 
                (instruction_i.b.funct3 == `FUNCT3_BLTU)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BLTU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
        end

        // BGEU
        else if ((instruction_i.b.opcode == `OPCODE_BGEU) && 
                (instruction_i.b.funct3 == `FUNCT3_BGEU)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BGEU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_B;
        end

        // LB
        else if ((instruction_i.i.opcode == `OPCODE_LB) && 
                (instruction_i.i.funct3 == `FUNCT3_LB)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl                      = LS_BYTE;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // LH
        else if ((instruction_i.i.opcode == `OPCODE_LH) && 
                (instruction_i.i.funct3 == `FUNCT3_LH)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl                      = LS_HALFWORD;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // LW
        else if ((instruction_i.i.opcode == `OPCODE_LW) && 
                (instruction_i.i.funct3 == `FUNCT3_LW)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl                      = LS_WORD;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // LD
        else if ((instruction_i.i.opcode == `OPCODE_LD) && 
                (instruction_i.i.funct3 == `FUNCT3_LD)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl                      = LS_DOUBLEWORD;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // LBU
        else if ((instruction_i.i.opcode == `OPCODE_LBU) && 
                (instruction_i.i.funct3 == `FUNCT3_LBU)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl                      = LS_BYTE_U;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // LHU
        else if ((instruction_i.i.opcode == `OPCODE_LHU) && 
                (instruction_i.i.funct3 == `FUNCT3_LHU)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl                      = LS_HALFWORD_U;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // LWU
        else if ((instruction_i.i.opcode == `OPCODE_LWU) && 
                (instruction_i.i.funct3 == `FUNCT3_LWU)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl                      = LS_WORD_U;
            rs1_req                     = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // SB
        else if ((instruction_i.s.opcode == `OPCODE_SB) && 
                (instruction_i.s.funct3 == `FUNCT3_SB)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            eu_ctl                      = LS_BYTE;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_S;
        end

        // SH
        else if ((instruction_i.s.opcode == `OPCODE_SH) && 
                (instruction_i.s.funct3 == `FUNCT3_SH)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            eu_ctl                      = LS_HALFWORD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_S;
        end

        // SW
        else if ((instruction_i.s.opcode == `OPCODE_SW) && 
                (instruction_i.s.funct3 == `FUNCT3_SW)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            eu_ctl                      = LS_WORD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_S;
        end

        // SD
        else if ((instruction_i.s.opcode == `OPCODE_SD) && 
                (instruction_i.s.funct3 == `FUNCT3_SD)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            eu_ctl                      = LS_DOUBLEWORD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_format                  = IMM_TYPE_S;
        end

        // ADDI
        else if ((instruction_i.i.opcode == `OPCODE_ADDI) && 
                (instruction_i.i.funct3 == `FUNCT3_ADDI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_ADD;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // ADDIW
        else if ((instruction_i.i.opcode == `OPCODE_ADDIW) && 
                (instruction_i.i.funct3 == `FUNCT3_ADDIW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_ADDW;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // SLTI
        else if ((instruction_i.i.opcode == `OPCODE_SLTI) && 
                (instruction_i.i.funct3 == `FUNCT3_SLTI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLT;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end
        
        // SLTIU
        else if ((instruction_i.i.opcode == `OPCODE_SLTIU) && 
                (instruction_i.i.funct3 == `FUNCT3_SLTIU)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLTU;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // XORI
        else if ((instruction_i.i.opcode == `OPCODE_XORI) && 
                (instruction_i.i.funct3 == `FUNCT3_XORI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_XOR;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // ORI
        else if ((instruction_i.i.opcode == `OPCODE_ORI) && 
                (instruction_i.i.funct3 == `FUNCT3_ORI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_OR;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // ANDI
        else if ((instruction_i.i.opcode == `OPCODE_ANDI) && 
                (instruction_i.i.funct3 == `FUNCT3_ANDI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_AND;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // SLLIW
        else if ((instruction_i.i.opcode == `OPCODE_SLLIW) && 
                (instruction_i.i.funct3 == `FUNCT3_SLLIW) &&
                (instruction_i.i.imm11[31:25] == 7'b0000000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLLW;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // SLLI
        else if ((instruction_i.i.opcode == `OPCODE_SLLI) && 
                (instruction_i.i.funct3 == `FUNCT3_SLLI) &&
                (instruction_i.i.imm11[31:26] == 6'b000000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLL;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // SRLIW
        else if ((instruction_i.i.opcode == `OPCODE_SRLIW) && 
                (instruction_i.i.funct3 == `FUNCT3_SRLIW) &&
                (instruction_i.i.imm11[31:25] == 7'b0000000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRLW;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // SRLI
        else if ((instruction_i.i.opcode == `OPCODE_SRLI) && 
                (instruction_i.i.funct3 == `FUNCT3_SRLI) &&
                (instruction_i.i.imm11[31:26] == 6'b000000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRL;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // SRAIW
        else if ((instruction_i.i.opcode == `OPCODE_SRAIW) && 
                (instruction_i.i.funct3 == `FUNCT3_SRAIW) &&
                (instruction_i.i.imm11[31:25] == 7'b0100000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRAW;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // SRAI
        else if ((instruction_i.i.opcode == `OPCODE_SRAI) && 
                (instruction_i.i.funct3 == `FUNCT3_SRAI) &&
                (instruction_i.i.imm11[31:26] == 6'b010000)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRA;
            rs1_req                     = 1'b1;
            rs2_is_imm                  = 1'b1;
            imm_format                  = IMM_TYPE_I;
            regstat_upd                 = 1'b1;
        end

        // ADDW
        else if ((instruction_i.r.opcode == `OPCODE_ADDW) && 
                (instruction_i.r.funct3 == `FUNCT3_ADDW) && 
                (instruction_i.r.funct7 == `FUNCT7_ADDW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_ADDW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // SUBW
        else if ((instruction_i.r.opcode == `OPCODE_SUBW) && 
                (instruction_i.r.funct3 == `FUNCT3_SUBW) && 
                (instruction_i.r.funct7 == `FUNCT7_SUBW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SUBW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // ADD
        else if ((instruction_i.r.opcode == `OPCODE_ADD) && 
            (instruction_i.r.funct3 == `FUNCT3_ADD) && 
            (instruction_i.r.funct7 == `FUNCT7_ADD)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_ADD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // SUB
        else if ((instruction_i.r.opcode == `OPCODE_SUB) && 
                (instruction_i.r.funct3 == `FUNCT3_SUB) && 
                (instruction_i.r.funct7 == `FUNCT7_SUB)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SUB;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // SLLW
        else if ((instruction_i.r.opcode == `OPCODE_SLLW) && 
                (instruction_i.r.funct3 == `FUNCT3_SLLW) && 
                (instruction_i.r.funct7 == `FUNCT7_SLLW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLLW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // SLL
        else if ((instruction_i.r.opcode == `OPCODE_SLL) && 
                (instruction_i.r.funct3 == `FUNCT3_SLL) && 
                (instruction_i.r.funct7 == `FUNCT7_SLL)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLL;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // SLT
        else if ((instruction_i.r.opcode == `OPCODE_SLT) && 
                (instruction_i.r.funct3 == `FUNCT3_SLT) && 
                (instruction_i.r.funct7 == `FUNCT7_SLT)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLT;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // SLTU
        else if ((instruction_i.r.opcode == `OPCODE_SLTU) && 
                (instruction_i.r.funct3 == `FUNCT3_SLTU) && 
                (instruction_i.r.funct7 == `FUNCT7_SLTU)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLTU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // XOR
        else if ((instruction_i.r.opcode == `OPCODE_XOR) && 
                (instruction_i.r.funct3 == `FUNCT3_XOR) && 
                (instruction_i.r.funct7 == `FUNCT7_XOR)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_XOR;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // SRLW
        else if ((instruction_i.r.opcode == `OPCODE_SRLW) && 
                (instruction_i.r.funct3 == `FUNCT3_SRLW) && 
                (instruction_i.r.funct7 == `FUNCT7_SRLW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRLW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // SRL
        else if ((instruction_i.r.opcode == `OPCODE_SRL) && 
                (instruction_i.r.funct3 == `FUNCT3_SRL) && 
                (instruction_i.r.funct7 == `FUNCT7_SRL)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRL;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // SRAW
        else if ((instruction_i.r.opcode == `OPCODE_SRAW) && 
                (instruction_i.r.funct3 == `FUNCT3_SRAW) && 
                (instruction_i.r.funct7 == `FUNCT7_SRAW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRAW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // SRA
        else if ((instruction_i.r.opcode == `OPCODE_SRA) && 
                (instruction_i.r.funct3 == `FUNCT3_SRA) && 
                (instruction_i.r.funct7 == `FUNCT7_SRA)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRA;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // OR
        else if ((instruction_i.r.opcode == `OPCODE_OR) && 
                (instruction_i.r.funct3 == `FUNCT3_OR) && 
                (instruction_i.r.funct7 == `FUNCT7_OR)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_OR;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // AND
        else if ((instruction_i.r.opcode == `OPCODE_AND) && 
                (instruction_i.r.funct3 == `FUNCT3_AND) && 
                (instruction_i.r.funct7 == `FUNCT7_AND)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_AND;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // FENCE
        else if ((instruction_i.i.opcode == `OPCODE_FENCE) && 
                (instruction_i.i.funct3 == `FUNCT3_FENCE) && 
                (instruction_i[30 -: 4] == `FENCE_FM_LSBS) && 
                (instruction_i.i.rs1 == `FENCE_RS1) && 
                (instruction_i.i.rd == `FENCE_RD)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
        end

        // ECALL
        else if ((instruction_i.i.opcode == `OPCODE_ECALL) && 
                (instruction_i.i.funct3 == `FUNCT3_ECALL) && 
                (instruction_i.i.imm11 == `ECALL_IMM) && 
                (instruction_i.i.rs1 == `ECALL_RS1) && 
                (instruction_i.i.rd == `ECALL_RD)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
        end

        // EBREAK
        else if ((instruction_i.i.opcode == `OPCODE_EBREAK) && 
                (instruction_i.i.funct3 == `FUNCT3_EBREAK) && 
                (instruction_i.i.imm11 == `EBREAK_IMM) && 
                (instruction_i.i.rs1 == `EBREAK_RS1) && 
                (instruction_i.i.rd == `EBREAK_RD)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            except_raised               = 1'b1;
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
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
        end

        // RV64 Zicsr
        // ----------

        // CSRRW
        else if ((instruction_i.i.opcode == `OPCODE_CSRRW) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRW)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_OPERANDS_ONLY;
            rs1_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // CSRRS
        else if ((instruction_i.i.opcode == `OPCODE_CSRRS) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRS)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_OPERANDS_ONLY;
            rs1_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // CSRRC
        else if ((instruction_i.i.opcode == `OPCODE_CSRRC) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRC)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_OPERANDS_ONLY;
            rs1_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end

        // CSRRWI
        else if ((instruction_i.i.opcode == `OPCODE_CSRRWI) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRWI)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            imm_format                  = IMM_TYPE_RS1;
            regstat_upd                 = 1'b1;
        end

        // CSRRSI
        else if ((instruction_i.i.opcode == `OPCODE_CSRRSI) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRSI)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            imm_format                  = IMM_TYPE_RS1;
            regstat_upd                 = 1'b1;
        end

        // CSRRCI
        else if ((instruction_i.i.opcode == `OPCODE_CSRRCI) && 
                (instruction_i.i.funct3 == `FUNCT3_CSRRCI)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            imm_format                  = IMM_TYPE_RS1;
            regstat_upd                 = 1'b1;
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
            eu_ctl[MULT_CTL_LEN-1:0]    = MULT_MUL;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        
        // MULW
        else if ((instruction_i.r.opcode == `OPCODE_MULW) &&
                (instruction_i.r.funct3 == `FUNCT3_MULW) &&
                (instruction_i.r.funct7 == `FUNCT7_MULW)) begin
            assigned_eu                 = EU_INT_MULT;
            eu_ctl[MULT_CTL_LEN-1:0]    = MULT_MULW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        
        // MULH
        else if ((instruction_i.r.opcode == `OPCODE_MULH) &&
                (instruction_i.r.funct3 == `FUNCT3_MULH) &&
                (instruction_i.r.funct7 == `FUNCT7_MULH)) begin
            assigned_eu                 = EU_INT_MULT;
            eu_ctl[MULT_CTL_LEN-1:0]    = MULT_MULH;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        
        // MULHSU
        else if ((instruction_i.r.opcode == `OPCODE_MULHSU) &&
                (instruction_i.r.funct3 == `FUNCT3_MULHSU) &&
                (instruction_i.r.funct7 == `FUNCT7_MULHSU)) begin
            assigned_eu                 = EU_INT_MULT;
            eu_ctl[MULT_CTL_LEN-1:0]    = MULT_MULHSU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        
        // MULHU
        else if ((instruction_i.r.opcode == `OPCODE_MULHU) &&
                (instruction_i.r.funct3 == `FUNCT3_MULHU) &&
                (instruction_i.r.funct7 == `FUNCT7_MULHU)) begin
            assigned_eu                 = EU_INT_MULT;
            eu_ctl[MULT_CTL_LEN-1:0]    = MULT_MULHU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
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
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
        end

        // SRET
        else if ((instruction_i.r.opcode == `OPCODE_SRET) && 
                (instruction_i.r.funct3 == `FUNCT3_SRET) && 
                (instruction_i.r.funct7 == `FUNCT7_SRET) && 
                (instruction_i.r.rs2 == `SRET_RS2) && 
                (instruction_i.r.rs1 == `SRET_RS1) && 
                (instruction_i.r.rd == `SRET_RD)) begin
            if (mstatus_tsr_i) begin
                except_raised           = 1'b1;
                except_code_t           = E_ILLEGAL_INSTRUCTION;
            end else begin
                stall_possible          = 1'b1;
                assigned_eu             = EU_NONE;
                res_ready               = 1'b1;
            end
        end

        // MRET
        else if ((instruction_i.r.opcode == `OPCODE_MRET) && 
                (instruction_i.r.funct3 == `FUNCT3_MRET) && 
                (instruction_i.r.funct7 == `FUNCT7_MRET) && 
                (instruction_i.r.rs2 == `MRET_RS2) && 
                (instruction_i.r.rs1 == `MRET_RS1) && 
                (instruction_i.r.rd == `MRET_RD)) begin
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            stall_possible              = 1'b1;
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
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            stall_possible              = 1'b1;
        end

        // Supervisor Memory-Management Instructions
        // -----------------------------------------

        // SFENCE.VMA
        else if ((instruction_i.r.opcode == `OPCODE_SFENCE_VMA) && 
                (instruction_i.r.funct3 == `FUNCT3_SFENCE_VMA) && 
                (instruction_i.r.funct7 == `FUNCT7_SFENCE_VMA) && 
                (instruction_i.r.rd == `SFENCE_VMA_RD)) begin
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            stall_possible              = 1'b1;
        end

        // Hypervisor Memory-Management Instructions
        // -----------------------------------------

        // HFENCE.BVMA
        else if ((instruction_i.r.opcode == `OPCODE_HFENCE_BVMA) && 
                (instruction_i.r.funct3 == `FUNCT3_HFENCE_BVMA) && 
                (instruction_i.r.funct7 == `FUNCT7_HFENCE_BVMA) && 
                (instruction_i.r.rd == `HFENCE_BVMA_RD)) begin
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            stall_possible              = 1'b1;
        end

        // HFENCE.GVMA
        else if ((instruction_i.r.opcode == `OPCODE_HFENCE_GVMA) && 
                (instruction_i.r.funct3 == `FUNCT3_HFENCE_GVMA) && 
                (instruction_i.r.funct7 == `FUNCT7_HFENCE_GVMA) && 
                (instruction_i.r.rd == `HFENCE_GVMA_RD)) begin
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            stall_possible              = 1'b1;
        end

    `endif /* LEN5_PRIVILEGED_EN */
        
        // UNSUPPORTED INSTRUCTION
        // -----------------------

        else begin
            assigned_eu                 = EU_NONE;
            except_raised               = 1'b1;  
            except_code                 = E_ILLEGAL_INSTRUCTION;
        end
    end

    // -----------------
    // OUTPUT GENERATION
    // -----------------
    assign except_raised_o          = except_raised;
    assign except_code_o            = except_code;
    assign res_ready_o              = res_ready;
    assign stall_possible_o         = stall_possible;

    assign eu_o                     = assigned_eu;
    assign eu_ctl_o                 = eu_ctl;
    assign fp_rs_o                  = rs_fp;
    assign rs1_req_o                = rs1_req;
    assign rs1_is_pc_o              = rs1_is_pc;
    assign rs2_req_o                = rs2_req;
    assign rs2_is_imm_o             = rs2_is_imm;
`ifdef LEN5_FP_EN
    assign rs3_req_o                = rs3_req;
`endif /* LEN5_FP_EN */
    assign imm_format_o             = imm_format;
    assign regstat_upd_o            = regstat_upd;

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    /* Assertions here */
    `endif
    
endmodule
