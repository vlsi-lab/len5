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
// File: mmm_pkg.sv
// Author: Marco Andorno
//         Matteo Perotti
//         Michele Caon
// Date: 26/07/2019

`ifndef LEN5_PKG_
`define LEN5_PKG_

// LEN5 compilation switches
`include "len5_config.svh"

package len5_pkg;

    // Global constants
    localparam ILEN = 32; // instruction length
    localparam OFFSET = $clog2(ILEN/8); // 2 LSB of addresses are always 0, so no use in using them for indexing
    localparam XLEN = 64;
    localparam FLEN = 64;

    /* Instruction fileds width */
    localparam OPCODE_LEN   = 7;
    localparam FUNCT2_LEN   = 2;
    localparam FUNCT3_LEN   = 3;
    localparam FUNCT7_LEN   = 7;
    localparam B_IMM        = 12;    // B-type immediate length
    localparam I_IMM        = 12;    // I-type immediate length
    localparam S_IMM        = I_IMM; // S-type immediate length
    localparam U_IMM        = 20;    // U-type immediate length
    localparam J_IMM        = U_IMM; // J-type immediate length
    localparam [ILEN-1:0] NOP = 'h13;

    // -------------------
    // INSTRUCTION FORMATS
    // -------------------

    // R-type instructions
    typedef struct packed {
        logic [31:25]   funct7;
        logic [24:20]   rs2;
        logic [19:15]   rs1;
        logic [14:12]   funct3;
        logic [11:7]    rd;
        logic [6:0]     opcode;
    } instr_r_type_t;

    // R4-type instructions
    typedef struct packed {
        logic [31:27]   rs3;
        logic [26:25]   funct2;
        logic [24:20]   rs2;
        logic [19:15]   rs1;
        logic [14:12]   funct3;
        logic [11:7]    rd;
        logic [6:0]     opcode;
    } instr_r4_type_t;

    // I-type instructions
    typedef struct packed {
        logic [31:20]   imm11;
        logic [19:15]   rs1;
        logic [14:12]   funct3;
        logic [11:7]    rd;
        logic [6:0]     opcode;
    } instr_i_type_t;

    // S-type instructions
    typedef struct packed {
        logic [31:25]   imm11;
        logic [24:20]   rs2;
        logic [19:15]   rs1;
        logic [14:12]   funct3;
        logic [11:7]    imm4;
        logic [6:0]     opcode;
    } instr_s_type_t;

    // B-type instructions
    typedef struct packed {
        logic [31:31]   imm12;
        logic [30:25]   imm10;
        logic [24:20]   rs2;
        logic [19:15]   rs1;
        logic [14:12]   funct3;
        logic [11:8]    imm4;
        logic [7:7]     imm11;
        logic [6:0]     opcode;
    } instr_b_type_t;

    // U-type instructions
    typedef struct packed {
        logic [31:12]   imm31;
        logic [11:7]    rd;
        logic [6:0]     opcode;
    } instr_u_type_t;

    // J-type instructions
    typedef struct packed {
        logic [31:31]   imm20;
        logic [30:21]   imm10;
        logic [20:20]   imm11;
        logic [19:12]   imm19;
        logic [11:7]    rd;
        logic [6:0]     opcode;
    } instr_j_type_t;

    // Instruction union type
    typedef union packed {
        instr_r_type_t  r;
        instr_r4_type_t r4;
        instr_i_type_t  i;
        instr_s_type_t  s;
        instr_b_type_t  b;
        instr_u_type_t  u;
        instr_j_type_t  j;
    } instr_t;

    // --------------
    // I-cache
    // --------------
    localparam ICACHE_OFFSET = 4; // for 16-instruction lines
    localparam ICACHE_INSTR = 1 << ICACHE_OFFSET;

    // icache output struct
    typedef struct packed {
        logic [XLEN-1:0]                    pc;
        logic [ICACHE_INSTR-1:0][ILEN-1:0]  line;
    } icache_out_t;

    // --------------
    // Frontend
    // --------------
    // instruction selector enums
    typedef enum logic [1:0] { current_pc = 'h0, prev_pc = 'h1, line_pc = 'h2 } pc_src_t;
    typedef enum logic [1:0] { cache_out = 'h0, line_reg = 'h1, line_bak = 'h2 } line_src_t;

    // prediction structure
    typedef struct packed {
        logic [XLEN-1:0]  pc;
        logic [XLEN-1:0]  target;
        logic             taken;
    } prediction_t;

    // resolution structure
    typedef struct packed {
        logic [XLEN-1:0]  pc;
        logic [XLEN-1:0]  target;
        logic             taken;
        logic             valid;
        logic             mispredict;
    } resolution_t;

    // -----------
    // Branch unit
    // -----------
    localparam BRANCH_TYPE_LEN = 3;
    typedef enum logic [BRANCH_TYPE_LEN-1:0] {
        BEQ   = 'h0,
        BNE   = 'h1,
        BLT   = 'h2,
        BGE   = 'h3,
        BLTU  = 'h4,
        BGEU  = 'h5
    } branch_type_t;

    //-----\\
    // CSR \\
    //-----\\

    typedef enum logic [1:0] {
        M, // machine mode
        S, // supervisor mode
        U  // user mode
    } priv_e;

    // ------------------
    // EXECUTION PIPELINE
    // ------------------

    // GLOBAL
    localparam XREG_NUM = 32; // number of integer gp registers
    localparam REG_IDX_LEN = $clog2(XREG_NUM); // Register file address width

    localparam FREG_NUM = 32; // number of floating-point registers
    localparam FREG_IDX_LEN = $clog2(FREG_NUM); // Floating point register file address width

    // ISSUE QUEUE
    localparam IQ_DEPTH = 4; // number of entries in the issue queue. This may or may not be a power of 2 (power of 2 recommended)

    // LOAD/STORE UNIT
    localparam LDBUFF_DEPTH = 4; // number of entries in the load buffer
    localparam STBUFF_DEPTH = 4; // number of entries in the store buffer

    // ROB
    localparam ROB_DEPTH = 4; // Number of entries in the ROB. This also tells the number of instruction that coexist in the execution pipeline at the same time

    // RESERVATION STATIONS
    localparam ALU_RS_DEPTH     = 4;
    localparam MULT_RS_DEPTH    = 4;
    localparam DIV_RS_DEPTH     = 4;
    localparam FPU_RS_DEPTH     = 4;
    localparam BU_RS_DEPTH      = 4;
    localparam OP_ONLY_RS_DEPTH = 2;

endpackage

`endif /* LEN5_PKG_ */
