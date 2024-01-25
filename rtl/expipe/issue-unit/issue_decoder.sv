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
`ifndef SYNTHESIS
`include "uvm_macros.svh"
import uvm_pkg::*;
`endif

/* Include instruction macros */
`include "instr_macros.svh"

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module issue_decoder (
    // Instruction from the issue logic
    input   instr_t         instruction_i,    // the issuing instruction
    input   csr_priv_t      priv_mode_i,      // current privilege mode

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
    output  imm_format_t    imm_format_o      // immediate format
);

    // INTERNAL SIGNALS
    // ----------------
    // Exceptions
    logic           except_raised;
    except_code_t   except_code;

    // Main decoder (opcode and special cases)
    issue_dec_sel_t dec_sel;
    logic           op_sel_32;  // select 32-bit operation
    issue_type_t    issue_type;
    issue_eu_t      assigned_eu;
    eu_ctl_t        eu_ctl;
    logic           rs1_req; 
    logic           rs1_is_pc;      // for AUIPC
    logic           rs2_req;
    logic           rs2_is_imm;     // for i-type ALU instr
`ifdef LEN5_FP_EN
    logic           rs3_req;
`endif /* LEN5_FP_EN */
    imm_format_t    imm_format;
    logic           skip_eu;
    logic           opcode_except;

    // Exception control
    except_code_t   system_except_code;
    
    // EU control decoders
    logic           alu_ctl_except;
    alu_ctl_t       alu_ctl, alu32_ctl;
`ifdef LEN5_M_EN
    logic           mult_ctl_except;
    mult_ctl_t      mult_ctl, mult32_ctl;
    logic           div_ctl_except;
    div_ctl_t       div_ctl, div32_ctl;
`endif /* `LEN5_M_EN */
    logic           branch_ctl_except;
    branch_ctl_t    branch_ctl;
    ldst_width_t    ldst_ctl;
    logic           ldst_ctl_except;

    // ------------------
    // INSTRUCTION DECODE
    // ------------------
    // New supported instructions can be added here. The necessary defines must
    // be appended to the 'instr_macros.svh' file.

    // OPCODE decoder
    // --------------
    always_comb begin: instr_format_logic
        // DEFAULT VALUES 
        dec_sel                     = ISSUE_DEC_SEL_MAIN;
        op_sel_32                   = 1'b0;
        issue_type                  = ISSUE_TYPE_NONE;
        skip_eu                     = 1'b0;
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
        opcode_except               = 1'b0;
        except_code                 = E_ILLEGAL_INSTRUCTION;

        unique case (instruction_i.i.opcode)
            `OPCODE_OP_IMM: begin
                rs1_req         = 1'b1;
                rs2_is_imm      = 1'b1;
                imm_format      = IMM_TYPE_I;
                issue_type      = ISSUE_TYPE_INT;
                dec_sel         = ISSUE_DEC_SEL_ALU;
                assigned_eu     = EU_INT_ALU;
                // Skip nops
                if ({instruction_i.i.imm11, instruction_i.i.rs1, instruction_i.i.funct3, instruction_i.i.rd} == '0)
                    skip_eu     = 1'b1;
            end
            `OPCODE_OP_IMM_32: begin
                op_sel_32       = 1'b1;
                rs1_req         = 1'b1;
                rs2_is_imm      = 1'b1;
                imm_format      = IMM_TYPE_I;
                issue_type      = ISSUE_TYPE_INT;
                dec_sel         = ISSUE_DEC_SEL_ALU;
                assigned_eu     = EU_INT_ALU;
            end
            `OPCODE_OP: begin
                rs1_req         = 1'b1;
                rs2_req         = 1'b1;
                issue_type      = ISSUE_TYPE_INT;
                unique case (instruction_i.r.funct7)
                    `FUNCT7_OP, `FUNCT7_OP_ALT: begin
                        assigned_eu = EU_INT_ALU;
                        dec_sel     = ISSUE_DEC_SEL_ALU;
                    end
                `ifdef LEN5_M_EN
                    `FUNCT7_M: begin
                        if (instruction_i.r.funct3[14]) begin
                            assigned_eu = EU_INT_DIV;
                            dec_sel     = ISSUE_DEC_SEL_DIV;
                        end else begin
                            assigned_eu = EU_INT_MULT;
                            dec_sel     = ISSUE_DEC_SEL_MULT;
                        end
                    end
                `endif /* LEN5_M_EN */
                    default: begin
                        opcode_except   = 1'b1;
                    end
                endcase
            end
            `OPCODE_OP_32: begin
                rs1_req         = 1'b1;
                rs2_req         = 1'b1;
                op_sel_32       = 1'b1;
                issue_type      = ISSUE_TYPE_INT;
                unique case (instruction_i.r.funct7)
                    `FUNCT7_OP, `FUNCT7_OP_ALT: begin
                        assigned_eu = EU_INT_ALU;
                        dec_sel     = ISSUE_DEC_SEL_ALU;
                    end
                `ifdef LEN5_M_EN
                    `FUNCT7_M: begin
                        if (instruction_i.r.funct3[14]) begin
                            assigned_eu = EU_INT_DIV;
                            dec_sel     = ISSUE_DEC_SEL_DIV;
                        end else begin
                            assigned_eu = EU_INT_MULT;
                            dec_sel     = ISSUE_DEC_SEL_MULT;
                        end
                    end
                `endif /* LEN5_M_EN */
                    default: opcode_except   = 1'b1;
                endcase
            end
            `OPCODE_LUI: begin
                skip_eu         = 1'b1;
                imm_format      = IMM_TYPE_U;
                issue_type      = ISSUE_TYPE_LUI;
            end
            `OPCODE_AUIPC: begin
                assigned_eu     = EU_INT_ALU;
                eu_ctl.alu      = ALU_ADD;
                imm_format      = IMM_TYPE_U;
                rs1_is_pc       = 1'b1;
                rs2_is_imm      = 1'b1;
                issue_type      = ISSUE_TYPE_INT;
            end
            `OPCODE_JAL: begin
                assigned_eu     = EU_BRANCH_UNIT;
                eu_ctl.bu       = JAL;
                imm_format      = IMM_TYPE_J;
                issue_type      = ISSUE_TYPE_JUMP;
            end
            `OPCODE_JALR: begin
                assigned_eu     = EU_BRANCH_UNIT;
                eu_ctl.bu       = JALR;
                rs1_req         = 1'b1;
                imm_format      = IMM_TYPE_I;
                issue_type      = ISSUE_TYPE_JUMP;
            end
            `OPCODE_BRANCH: begin
                assigned_eu     = EU_BRANCH_UNIT;
                rs1_req         = 1'b1;
                rs2_req         = 1'b1;
                imm_format      = IMM_TYPE_B;
                issue_type      = ISSUE_TYPE_BRANCH;
                dec_sel         = ISSUE_DEC_SEL_BRANCH;
            end
            `OPCODE_LOAD: begin
                assigned_eu     = EU_LOAD_BUFFER;
                dec_sel         = ISSUE_DEC_SEL_LS;
                rs1_req         = 1'b1;
                imm_format      = IMM_TYPE_I;
                issue_type      = ISSUE_TYPE_INT;
            end
            `OPCODE_STORE: begin
                assigned_eu     = EU_STORE_BUFFER;
                issue_type      = ISSUE_TYPE_STORE;
                dec_sel         = ISSUE_DEC_SEL_LS;
                rs1_req         = 1'b1;
                rs2_req         = 1'b1;
                imm_format      = IMM_TYPE_S;
            end
            `OPCODE_SYSTEM: begin
                skip_eu         = 1'b1;
                unique case (instruction_i.i.funct3)
                    `FUNCT3_CSRRC,
                    `FUNCT3_CSRRCI,
                    `FUNCT3_CSRRS,
                    `FUNCT3_CSRRSI,
                    `FUNCT3_CSRRW,
                    `FUNCT3_CSRRWI: begin
                        issue_type      = ISSUE_TYPE_CSR;
                        rs1_req         = 1'b1;
                    end
                    `FUNCT3_ZERO: begin
                        issue_type      = ISSUE_TYPE_STALL;
                        opcode_except   = 1'b1;
                        except_code     = system_except_code;
                    end
                    default: opcode_except = 1'b1;
                endcase
            end
            `OPCODE_MISC_MEM: begin
                // NOTE: No proper support so far
                if (instruction_i.r.funct3 == '0) begin
                    issue_type      = ISSUE_TYPE_STALL;
                    skip_eu         = 1'b1;
                end else begin
                    opcode_except = 1'b1;
                end
            end
        `ifdef LEN5_A_EN
        // TODO: add atomic instructions
            `OPCODE_AMO: begin
                
            end
        `endif /* LEN5_A_EN */
        `ifdef LEN5_FP_EN
            // Add floating-point support
            `OPCODE_LOAD_FP: begin
                
            end
            `OPCODE_STORE_FP: begin
                
            end
            `OPCODE_OP_FP: begin
                
            end
            `OPCODE_FMADD: begin
                
            end
            `OPCODE_FNMADD: begin
                
            end
            `OPCODE_FMSUB: begin
                
            end
            `OPCODE_FNMSUB: begin
                
            end: 
        `endif /* LEN5_FP_EN */
            default: begin
                skip_eu                     = 1'b1;
                issue_type                  = ISSUE_TYPE_EXCEPT;
                opcode_except               = 1'b1;
            end
        endcase
    end

    // FUNCT3 DECODERS
    // ---------------

    // ALU control decoders
    always_comb begin : alu_ctl_dec
        alu_ctl_except  = 1'b0;
        alu_ctl         = ALU_ADD;
        alu32_ctl       = ALU_ADDW;
        unique case (instruction_i.r.funct3)
            `FUNCT3_ADD: begin
                if (instruction_i.r.funct7 == `FUNCT7_SUB && 
                    instruction_i.r.opcode[5]) begin
                    alu_ctl     = ALU_SUB;
                    alu32_ctl   = ALU_SUBW;
                end else begin
                    alu_ctl     = ALU_ADD;
                    alu32_ctl   = ALU_ADDW;
                end
            end
            `FUNCT3_SLL: begin
                alu_ctl     = ALU_SLL;
                alu32_ctl   = ALU_SLLW;
            end
            `FUNCT3_SLT: begin 
                alu_ctl     = ALU_SLT;
                alu32_ctl   = ALU_SLT;
            end
            `FUNCT3_SLTU: begin
                alu_ctl     = ALU_SLTU;
                alu32_ctl   = ALU_SLTU;
            end
            `FUNCT3_XOR: begin
                alu_ctl     = ALU_XOR;
                alu32_ctl   = ALU_XOR;
            end
            `FUNCT3_SRA: begin
                unique case ({instruction_i.r.funct7[31:26], 1'b0})
                    `FUNCT7_SRA: begin
                        alu_ctl     = ALU_SRA;
                        alu32_ctl   = ALU_SRAW;
                        alu_ctl_except = instruction_i.r.opcode[3] & instruction_i.r.funct7[25];
                    end
                    `FUNCT7_SRL: begin
                        alu_ctl     = ALU_SRL;
                        alu32_ctl   = ALU_SRLW;
                        alu_ctl_except = instruction_i.r.opcode[3] & instruction_i.r.funct7[25];
                    end
                    default: alu_ctl_except = 1'b1;
                endcase
            end
            `FUNCT3_OR: begin
                alu_ctl     = ALU_OR;
                alu32_ctl   = ALU_OR;
            end
            `FUNCT3_AND: begin
                alu_ctl     = ALU_AND;
                alu32_ctl   = ALU_AND;
            end
            default: alu_ctl_except = 1'b1;
        endcase
    end

    // Load/store control decoder
    always_comb begin : ldst_ctl_dec
        ldst_ctl_except     = 1'b0;
        ldst_ctl            = LS_DOUBLEWORD;
        unique case (instruction_i.s.funct3)
            `FUNCT3_LB, `FUNCT3_LBU, `FUNCT3_SB:
                ldst_ctl = LS_BYTE;
            `FUNCT3_LH, `FUNCT3_LHU, `FUNCT3_SH:
                ldst_ctl = LS_HALFWORD;
            `FUNCT3_LW, `FUNCT3_LWU, `FUNCT3_SW:
                ldst_ctl = LS_WORD;
            `FUNCT3_LD, `FUNCT3_SD:
                ldst_ctl = LS_DOUBLEWORD;
            default: ldst_ctl_except = 1'b1;
        endcase
    end

    // Branch control decoder
    always_comb begin : bu_ctl_dec
        branch_ctl_except   = 1'b0;
        branch_ctl          = BEQ;
        unique case (instruction_i.r.funct3)
            `FUNCT3_BEQ:    branch_ctl  = BEQ;
            `FUNCT3_BNE:    branch_ctl  = BNE;
            `FUNCT3_BLT:    branch_ctl  = BLT;
            `FUNCT3_BGE:    branch_ctl  = BGE;
            `FUNCT3_BLTU:   branch_ctl  = BLTU;
            `FUNCT3_BGEU:   branch_ctl  = BGEU;
            default: branch_ctl_except  = 1'b1;
        endcase
    end

`ifdef LEN5_M_EN
    // MULT decoder
    always_comb begin : mult_ctl_dec
        mult_ctl_except = 1'b0;
        mult_ctl        = MULT_MUL;
        unique case (instruction_i.r.funct3)
            `FUNCT3_MUL: begin
                mult_ctl    = MULT_MUL;
                mult32_ctl  = MULT_MULW;
            end
            `FUNCT3_MULH: begin
                mult_ctl    = MULT_MULH;
                mult32_ctl  = MULT_MULH;
            end
            `FUNCT3_MULHSU: begin
                mult_ctl    = MULT_MULHU;
                mult32_ctl  = MULT_MULHU;
            end
            `FUNCT3_MULHU: begin
                mult_ctl    = MULT_MULHSU;
                mult32_ctl  = MULT_MULHSU;
            end
            default: mult_ctl_except = 1'b1;
        endcase
    end

    // DIV decoder
    always_comb begin : div_ctl_dec
        div_ctl_except = 1'b0;
        div_ctl        = DIV_DIV;
        unique case (instruction_i.r.funct3)
            `FUNCT3_DIV: begin
                div_ctl     = DIV_DIV;
                div32_ctl   = DIV_DIVW;
            end
            `FUNCT3_DIVU: begin
                div_ctl     = DIV_DIVU;
                div32_ctl   = DIV_DIVUW;
            end
            `FUNCT3_REM: begin
                div_ctl     = DIV_REM;
                div32_ctl   = DIV_REMW;
            end
            `FUNCT3_REMU: begin
                div_ctl     = DIV_REMU;
                div32_ctl   = DIV_REMUW;
            end
            default: div_ctl_except = 1'b1;
        endcase
    end
`endif /* LEN5_M_EN */
    
    // Decoder MUX
    // -----------
    always_comb begin : dec_mux
        unique case (dec_sel)
            ISSUE_DEC_SEL_ALU: begin
                except_raised   = alu_ctl_except;
                eu_ctl_o.alu    = (op_sel_32) ? alu32_ctl : alu_ctl;
            end
        `ifdef LEN5_M_EN
            ISSUE_DEC_SEL_MULT: begin
                except_raised   = mult_ctl_except;
                eu_ctl_o.mult   = (op_sel_32) ? mult32_ctl : mult_ctl;
            end
            ISSUE_DEC_SEL_DIV: begin
                except_raised   = div_ctl_except;
                eu_ctl_o.div    = (op_sel_32) ? div32_ctl : div_ctl;
            end
        `endif /* LEN5_M_EN */
            ISSUE_DEC_SEL_LS: begin
                except_raised   = ldst_ctl_except;
                eu_ctl_o.lsu    = ldst_ctl;
            end
            ISSUE_DEC_SEL_BRANCH: begin
                except_raised   = branch_ctl_except;
                eu_ctl_o.bu     = branch_ctl;
            end
            default: begin
                except_raised   = opcode_except;
                eu_ctl_o        = eu_ctl;
            end
        endcase
    end

    // -----------------
    // EXCEPTION CONTROL
    // -----------------

    // Privilege mode exception mux
    always_comb begin : system_except_mux
        unique case ({instruction_i.r.funct7, instruction_i.r.rs2, instruction_i.r.rs1})
            {`ECALL_IMM, `ECALL_RS1}: begin // ECALL
                system_except_code  = (priv_mode_i == PRIV_MODE_U) ? E_ENV_CALL_UMODE : E_ENV_CALL_MMODE;
            end
            {`EBREAK_IMM, `EBREAK_RS1}: begin // EBREAK
                system_except_code  = E_BREAKPOINT;
            end
            default: begin
                system_except_code  = E_UNKNOWN;
            end
        endcase
    end

    assign  issue_type_o        = (except_raised | opcode_except) ? ISSUE_TYPE_EXCEPT : issue_type;
    assign  skip_eu_o           = (except_raised | opcode_except) ? 1'b1 : skip_eu;

    // -----------------
    // OUTPUT GENERATION
    // -----------------
    assign  except_code_o        = except_code;
    assign  assigned_eu_o        = assigned_eu;
    assign  rs1_req_o            = rs1_req;
    assign  rs1_is_pc_o          = rs1_is_pc;
    assign  rs2_req_o            = rs2_req;
    assign  rs2_is_imm_o         = rs2_is_imm;
`ifdef LEN5_FP_EN
    assign  rs3_req_o            = rs3_req;
`endif /* LEN5_FP_EN */
    assign  imm_format_o         = imm_format;

    // ----------
    // ASSERTIONS
    // ----------
    `ifndef SYNTHESIS
    /* Assertions here */
    `endif
    
endmodule
