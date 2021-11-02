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
// File: issue_decoder.sv
// Author: Michele Caon
// Date: 13/11/2019

// Import UVM report macros
`include "uvm_macros.svh"
import uvm_pkg::*;

/* Include instruction macros */
`include "instr_macros.svh"

import len5_pkg::*;
import expipe_pkg::*;

module issue_decoder (
    // Instruction from the issue logic
    input   logic [ILEN-1:0]                issue_instruction_i,    // the issuing instruction opcode
    
    // Information to the issue logic
    output  logic                           issue_except_raised_o,  // an exception occurred during decoding
    output  except_code_t                   issue_except_code_o,    // exception code to send to the ROB
    output  logic                           issue_res_ready_o,      // force ready to commit in the ROB
    output  logic                           issue_stall_possible_o, // the instruction issue can be stall to save power

    output  issue_eu_t                      issue_eu_o,             // assigned EU
    output  logic [8-1:0]      				issue_eu_ctl_o,         // controls for the assigned EU
    output  logic                           issue_fp_rs_o,          // rs1 and rs2 refer to the floating point register file 
    output  logic                           issue_rs1_req_o,        // rs1 fetch is required
    output  logic                           issue_rs2_req_o,        // rs2 fetch is required
    output  logic                           issue_imm_req_o,        // immediate required 
    output  imm_format_t                    issue_imm_format_o,     // immediate format    
    output  logic                           issue_regstat_upd_o     // the register status must be updated              
);

    // DEFINITIONS

    logic                           except_raised; 
    except_code_t                   except_code;
    logic                           res_ready;
    logic                           stall_possible;
    issue_eu_t                      assigned_eu;
    logic [8-1:0]                   eu_ctl;
    logic                           rs_fp;
    logic                           rs1_req; 
    logic                           rs2_req;
    logic                           imm_req;
    imm_format_t                    imm_format;
    logic                           regstat_upd;

    logic [OPCODE_LEN -1:0]        instr_opcode;
    logic [FUNCT3_LEN -1:0]        instr_funct3;
    logic [FUNCT7_LEN -1:0]        instr_funct7;
    logic [REG_IDX_LEN-1:0]         instr_rs1, instr_rs2, instr_rd;
    logic [I_IMM-1:0]               instr_imm;

    //-----------------------------\\
    //----- OPCODE EXTRACTION -----\\
    //-----------------------------\\
    assign instr_opcode      = issue_instruction_i[OPCODE_LEN-1 : 0];
    assign instr_funct3      = issue_instruction_i[14 -: FUNCT3_LEN];
    assign instr_funct7      = issue_instruction_i[31 -: FUNCT7_LEN];

    //--------------------------------------\\
    //----- OPERAND ADDRESS EXTRACTION -----\\
    //--------------------------------------\\
    assign instr_rs1                = issue_instruction_i[19 -: REG_IDX_LEN];
    assign instr_rs2                = issue_instruction_i[24 -: REG_IDX_LEN];
    assign instr_rd                 = issue_instruction_i[11 -: REG_IDX_LEN];
    assign instr_imm                = issue_instruction_i[31 -: I_IMM];

    //------------------------------\\
    //----- INSTRUCTION DECODE -----\\
    //------------------------------\\
    // New supported instructions can be added here. The necessary defines must be appended to the 'instr_macros.svh' file. 

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
        rs2_req                     = 1'b0;
        imm_req                     = 1'b0;
        imm_format                  = IMM_SEXT;
        regstat_upd                 = 1'b0;

        // OPCODE ANALYSIS
        
        // R-FORMAT INSTRUCTIONS
        
        // ADD
        if ((instr_opcode == `OPCODE_ADD) && (instr_funct3 == `FUNCT3_ADD) && (instr_funct7 == `FUNCT7_ADD)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_ADD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // ADDW
        else if ((instr_opcode == `OPCODE_ADDW) && (instr_funct3 == `FUNCT3_ADDW) && (instr_funct7 == `FUNCT7_ADDW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_ADDW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // AND
        else if ((instr_opcode == `OPCODE_AND) && (instr_funct3 == `FUNCT3_AND) && (instr_funct7 == `FUNCT7_AND)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_AND;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // MRET
        else if ((instr_opcode == `OPCODE_MRET) && (instr_funct3 == `FUNCT3_MRET) && (instr_funct7 == `FUNCT7_MRET) && (instr_rs2 == `MRET_RS2) && (instr_rs1 == `MRET_RS1) && (instr_rd == `MRET_RD)) begin
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            stall_possible              = 1'b1;
        end
        // OR
        else if ((instr_opcode == `OPCODE_OR) && (instr_funct3 == `FUNCT3_OR) && (instr_funct7 == `FUNCT7_OR)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_OR;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // SFENCE_VMA
        else if ((instr_opcode == `OPCODE_SFENCE_VMA) && (instr_funct3 == `FUNCT3_SFENCE_VMA) && (instr_funct7 == `FUNCT7_SFENCE_VMA) && (instr_rd == `SFENCE_VMA_RD)) begin
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            stall_possible              = 1'b1;
        end
        // SLL
        else if ((instr_opcode == `OPCODE_SLL) && (instr_funct3 == `FUNCT3_SLL) && (instr_funct7 == `FUNCT7_SLL)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLL;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // SLLW
        else if ((instr_opcode == `OPCODE_SLLW) && (instr_funct3 == `FUNCT3_SLLW) && (instr_funct7 == `FUNCT7_SLLW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLLW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // SLT
        else if ((instr_opcode == `OPCODE_SLT) && (instr_funct3 == `FUNCT3_SLT) && (instr_funct7 == `FUNCT7_SLT)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLT;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // SLTU
        else if ((instr_opcode == `OPCODE_SLTU) && (instr_funct3 == `FUNCT3_SLTU) && (instr_funct7 == `FUNCT7_SLTU)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLTU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // SRA
        else if ((instr_opcode == `OPCODE_SRA) && (instr_funct3 == `FUNCT3_SRA) && (instr_funct7 == `FUNCT7_SRA)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRA;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // SRAW
        else if ((instr_opcode == `OPCODE_SRAW) && (instr_funct3 == `FUNCT3_SRAW) && (instr_funct7 == `FUNCT7_SRAW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRAW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // SRET
        else if ((instr_opcode == `OPCODE_SRET) && (instr_funct3 == `FUNCT3_SRET) && (instr_funct7 == `FUNCT7_SRET) && (instr_rs2 == `SRET_RS2) && (instr_rs1 == `SRET_RS1) && (instr_rd == `SRET_RD)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
        end
        // SRL
        else if ((instr_opcode == `OPCODE_SRL) && (instr_funct3 == `FUNCT3_SRL) && (instr_funct7 == `FUNCT7_SRL)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRL;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // SRLW
        else if ((instr_opcode == `OPCODE_SRLW) && (instr_funct3 == `FUNCT3_SRLW) && (instr_funct7 == `FUNCT7_SRLW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRLW;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // SUB
        else if ((instr_opcode == `OPCODE_SUB) && (instr_funct3 == `FUNCT3_SUB) && (instr_funct7 == `FUNCT7_SUB)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SUB;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // SUBW
        else if ((instr_opcode == `OPCODE_SUBW) && (instr_funct3 == `FUNCT3_SUBW) && (instr_funct7 == `FUNCT7_SUBW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SUB;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // WFI
        else if ((instr_opcode == `OPCODE_WFI) && (instr_funct3 == `FUNCT3_WFI) && (instr_funct7 == `FUNCT7_WFI) && (instr_rs2 == `WFI_RS2) && (instr_rs1 == `WFI_RS1) && (instr_rd == `WFI_RD)) begin
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            stall_possible              = 1'b1;
        end
        // XOR
        else if ((instr_opcode == `OPCODE_XOR) && (instr_funct3 == `FUNCT3_XOR) && (instr_funct7 == `FUNCT7_XOR)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_XOR;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            regstat_upd                 = 1'b1;
        end
            
        // I-FORMAT INSTRUCTIONS
            
        // NOP
        else if ((instr_opcode == `OPCODE_ADDI) && (instr_funct3 == `FUNCT3_ADDI) && (instr_rs1 == 0) && (instr_imm == 0)) begin
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            stall_possible              = 1'b1;
        end

        // ADDI
        else if ((instr_opcode == `OPCODE_ADDI) && (instr_funct3 == `FUNCT3_ADDI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_ADD;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end        

        // ADDIW
        else if ((instr_opcode == `OPCODE_ADDIW) && (instr_funct3 == `FUNCT3_ADDIW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_ADDW;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // ANDI
        else if ((instr_opcode == `OPCODE_ANDI) && (instr_funct3 == `FUNCT3_ANDI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_AND;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // CSRRC
        else if ((instr_opcode == `OPCODE_CSRRC) && (instr_funct3 == `FUNCT3_CSRRC)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            regstat_upd                 = 1'b1; // flush is required, so this might be useless
        end
        // CSRRCI
        else if ((instr_opcode == `OPCODE_CSRRCI) && (instr_funct3 == `FUNCT3_CSRRCI)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // CSRRS
        else if ((instr_opcode == `OPCODE_CSRRS) && (instr_funct3 == `FUNCT3_CSRRS)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // CSRRSI
        else if ((instr_opcode == `OPCODE_CSRRSI) && (instr_funct3 == `FUNCT3_CSRRSI)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // CSRRW
        else if ((instr_opcode == `OPCODE_CSRRW) && (instr_funct3 == `FUNCT3_CSRRW)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // CSRRWI
        else if ((instr_opcode == `OPCODE_CSRRWI) && (instr_funct3 == `FUNCT3_CSRRWI)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // FENCE
        else if ((instr_opcode == `OPCODE_FENCE) && (instr_funct3 == `FUNCT3_FENCE) && (issue_instruction_i[31 -: 4] == `FENCE_MSBS) && (instr_rs1 == `FENCE_RS1) && (instr_rd == `FENCE_RD)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
        end
        // FENCE_I
        else if ((instr_opcode == `OPCODE_FENCE_I) && (instr_funct3 == `FUNCT3_FENCE_I) && (instr_imm == `FENCE_I_IMM) && (instr_rs1 == `FENCE_I_RS1) && (instr_rd == `FENCE_I_RD)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
        end
        // JALR
        else if ((instr_opcode == `OPCODE_JALR) && (instr_funct3 == `FUNCT3_JALR)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // ORI
        else if ((instr_opcode == `OPCODE_ORI) && (instr_funct3 == `FUNCT3_ORI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_OR;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // SLLI
        else if ((instr_opcode == `OPCODE_SLLI) && (instr_funct3 == `FUNCT3_SLLI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLL;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SHAMT;
            regstat_upd                 = 1'b1;
        end
        // SLLIW
        else if ((instr_opcode == `OPCODE_SLLIW) && (instr_funct3 == `FUNCT3_SLLIW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLLW;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SHAMT;
            regstat_upd                 = 1'b1;
        end
        // SRAI
        else if ((instr_opcode == `OPCODE_SRAI) && (instr_funct3 == `FUNCT3_SRAI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRA;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SHAMT;
            regstat_upd                 = 1'b1;
        end
        // SRAIW
        else if ((instr_opcode == `OPCODE_SRAIW) && (instr_funct3 == `FUNCT3_SRAIW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRAW;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SHAMT;
            regstat_upd                 = 1'b1;
        end
        // SLTI
        else if ((instr_opcode == `OPCODE_SLTI) && (instr_funct3 == `FUNCT3_SLTI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLT;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // SLTIU
        else if ((instr_opcode == `OPCODE_SLTIU) && (instr_funct3 == `FUNCT3_SLTIU)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SLTU;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // SRLI
        else if ((instr_opcode == `OPCODE_SRLI) && (instr_funct3 == `FUNCT3_SRLI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRL;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SHAMT;
            regstat_upd                 = 1'b1;
        end
        // SRLIW
        else if ((instr_opcode == `OPCODE_SRLIW) && (instr_funct3 == `FUNCT3_SRLIW)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_SRLW;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SHAMT;
            regstat_upd                 = 1'b1;
        end
        // XORI
        else if ((instr_opcode == `OPCODE_XORI) && (instr_funct3 == `FUNCT3_XORI)) begin
            assigned_eu                 = EU_INT_ALU;
            eu_ctl[ALU_CTL_LEN-1:0]     = ALU_XOR;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // EBREAK
        else if ((instr_opcode == `OPCODE_EBREAK) && (instr_funct3 == `FUNCT3_EBREAK) && (instr_imm == `EBREAK_IMM) && (instr_rs1 == `EBREAK_RS1) && (instr_rd == `EBREAK_RD)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            except_raised               = 1'b1;
            except_code                 = E_BREAKPOINT;
        end
        // ECALL
        else if ((instr_opcode == `OPCODE_ECALL) && (instr_funct3 == `FUNCT3_ECALL) && (instr_imm == `ECALL_IMM) && (instr_rs1 == `ECALL_RS1) && (instr_rd == `ECALL_RD)) begin
            stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            res_ready                   = 1'b1;
        end
        // LB
        else if ((instr_opcode == `OPCODE_LB) && (instr_funct3 == `FUNCT3_LB)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl[LB_CTL_LEN-1:0]      = LS_BYTE;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // LBU
        else if ((instr_opcode == `OPCODE_LBU) && (instr_funct3 == `FUNCT3_LBU)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl[LB_CTL_LEN-1:0]      = LS_BYTE_U;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // LD
        else if ((instr_opcode == `OPCODE_LD) && (instr_funct3 == `FUNCT3_LD)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl[LB_CTL_LEN-1:0]      = LS_DOUBLEWORD;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // LH
        else if ((instr_opcode == `OPCODE_LH) && (instr_funct3 == `FUNCT3_LH)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl[LB_CTL_LEN-1:0]      = LS_HALFWORD;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // LHU
        else if ((instr_opcode == `OPCODE_LHU) && (instr_funct3 == `FUNCT3_LHU)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl[LB_CTL_LEN-1:0]      = LS_HALFWORD_U;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // LW
        else if ((instr_opcode == `OPCODE_LW) && (instr_funct3 == `FUNCT3_LW)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl[LB_CTL_LEN-1:0]      = LS_WORD;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
        // LWU
        else if ((instr_opcode == `OPCODE_LWU) && (instr_funct3 == `FUNCT3_LWU)) begin
            assigned_eu                 = EU_LOAD_BUFFER;
            eu_ctl[LB_CTL_LEN-1:0]      = LS_WORD_U;
            rs1_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            regstat_upd                 = 1'b1;
        end
            
        // S-FORMAT INSTRUCTIONS
        
        // SB
        else if ((instr_opcode == `OPCODE_SB) && (instr_funct3 == `FUNCT3_SB)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            eu_ctl[SB_CTL_LEN-1:0]      = LS_BYTE;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
        end 
        // SD
        else if ((instr_opcode == `OPCODE_SD) && (instr_funct3 == `FUNCT3_SD)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            eu_ctl[SB_CTL_LEN-1:0]      = LS_DOUBLEWORD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
        end 
        // SH
        else if ((instr_opcode == `OPCODE_SH) && (instr_funct3 == `FUNCT3_SH)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            eu_ctl[SB_CTL_LEN-1:0]      = LS_HALFWORD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
        end 
        // SW
        else if ((instr_opcode == `OPCODE_SW) && (instr_funct3 == `FUNCT3_SW)) begin
            assigned_eu                 = EU_STORE_BUFFER;
            eu_ctl[SB_CTL_LEN-1:0]      = LS_WORD;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
        end 

        // B-FORMAT INSTRUCTIONS
        // BEQ
        else if ((instr_opcode == `OPCODE_BEQ) && (instr_funct3 == `FUNCT3_BEQ)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BEQ;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
        end
        // BGE
        else if ((instr_opcode == `OPCODE_BGE) && (instr_funct3 == `FUNCT3_BGE)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BGE;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
        end
        // BGEU
        else if ((instr_opcode == `OPCODE_BGEU) && (instr_funct3 == `FUNCT3_BGEU)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BGEU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
        end
        // BLT
        else if ((instr_opcode == `OPCODE_BLT) && (instr_funct3 == `FUNCT3_BLT)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BLT;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
        end
        // BLTU
        else if ((instr_opcode == `OPCODE_BLTU) && (instr_funct3 == `FUNCT3_BLTU)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BLTU;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
        end
        // BNE
        else if ((instr_opcode == `OPCODE_BNE) && (instr_funct3 == `FUNCT3_BNE)) begin
            assigned_eu                 = EU_BRANCH_UNIT;
            eu_ctl[BU_CTL_LEN-1:0]      = BNE;
            rs1_req                     = 1'b1;
            rs2_req                     = 1'b1;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
        end

        // U-FORMAT INSTRUCTIONS 
        
        // AUIPC
        else if ((instr_opcode == `OPCODE_AUIPC)) begin
            // depending on how it's implemented, stalling the fetch and issue could be convenient or not
            // stall_possible              = 1'b1;
            assigned_eu                 = EU_NONE;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            res_ready                   = 1'b1;
            regstat_upd                 = 1'b1;
        end
        // LUI
        else if ((instr_opcode == `OPCODE_LUI)) begin
            assigned_eu                 = EU_NONE;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            res_ready                   = 1'b1;
            regstat_upd                 = 1'b1;
        end
            
        // J-FORMAT INSTRUCTIONS
        
        // JAL
        else if (instr_opcode == `OPCODE_JAL) begin
            assigned_eu                 = EU_NONE;
            imm_req                     = 1'b1;
            imm_format                  = IMM_SEXT;
            res_ready                   = 1'b1;
            regstat_upd                 = 1'b1;
        end 
        
        // UNKNOWN INSTRUCTIONS

        else begin
            assigned_eu                 = EU_NONE;
            except_raised               = 1'b1;  
            except_code                 = E_ILLEGAL_INSTRUCTION;
        end
    end

    //-----------------------------\\
    //----- OUTPUT GENERATION -----\\
    //-----------------------------\\
    assign issue_except_raised_o            = except_raised;
    assign issue_except_code_o              = except_code;
    assign issue_res_ready_o                = res_ready;
    assign issue_stall_possible_o           = stall_possible;

    assign issue_eu_o                       = assigned_eu;
    assign issue_eu_ctl_o                   = eu_ctl;
    assign issue_fp_rs_o                    = rs_fp;
    assign issue_rs1_req_o                  = rs1_req;
    assign issue_rs2_req_o                  = rs2_req;
    assign issue_imm_req_o                  = imm_req;
    assign issue_imm_format_o               = imm_format;
    assign issue_regstat_upd_o              = regstat_upd;

    //----------------------\\
    //----- ASSERTIONS -----\\
    //----------------------\\
    `ifndef SYNTHESIS
    always @(except_code) begin
        assert ((except_code != E_ILLEGAL_INSTRUCTION) && (except_code != E_BREAKPOINT)) 
        else   `uvm_warning("ISSUE", $sformatf("Issuing instruction unknown opcode: %b", issue_instruction_i))
    end
    `endif
    
endmodule
