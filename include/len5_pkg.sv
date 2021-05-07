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

`ifndef LEN5_PKG
`define LEN5_PKG

package len5_pkg;

  // Global constants
  localparam ILEN = 32; // instruction length
  localparam OFFSET = 2;//$clog2(ILEN/8); // 2 LSB of addresses are always 0, so no use in using them for indexing
  localparam XLEN = 64;
  localparam FLEN = 64;
  localparam [XLEN-1:0] BOOT_PC = 'h0; // starting PC (to be defined)

    /* Instruction fileds width */
  localparam OPCODE_LEN   = 7;
  localparam FUNCT3_LEN   = 3;
  localparam FUNCT7_LEN   = 7;
  localparam B_IMM        = 12;    // B-type immediate length
  localparam I_IMM        = 12;    // I-type immediate length
  localparam S_IMM        = I_IMM; // S-type immediate length
  localparam U_IMM        = 20;    // U-type immediate length
  localparam J_IMM        = U_IMM; // J-type immediate length
  localparam [ILEN-1:0] NOP = 'h13;

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
  typedef enum logic [5:0] {
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



  //------------------------------\\
  //----- EXECUTION PIPELINE -----\\
  //------------------------------\\
  
  // GLOBAL
  localparam XREG_NUM = 32; // number of integer gp registers
  localparam REG_IDX_LEN = 5;//$clog2(XREG_NUM); // Register file address width

  localparam FREG_NUM = 32; // number of floating-point registers
  localparam FREG_IDX_LEN = 5;//$clog2(FREG_NUM); // Floating point register file address width

  // Number of execution units (and reservation stations)
  localparam EU_N = 8; // load buffer, store buffer, branch unit, ALU, MULT, DIV, FPU, operands only

  // ISSUE QUEUE
  localparam IQ_DEPTH = 8; // number of entries in the issue queue. This may or may not be a power of 2 (power of 2 recommended)

  // LOAD/STORE UNIT
  localparam LDBUFF_DEPTH = 8; // number of entries in the load buffer
  localparam STBUFF_DEPTH = 8; // number of entries in the store buffer

  // ROB
  localparam ROB_DEPTH = 16; // Number of entries in the ROB. This also tells the number of instruction that coexist in the execution pipeline at the same time

endpackage

`endif
