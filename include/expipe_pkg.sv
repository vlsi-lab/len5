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
// File: expipe_pkg.sv
// Author: Michele Caon
// Date: 17/10/2019

`ifndef EXPIPE_PKG
`define EXPIPE_PKG

// LEN5 compilation switches
`include "len5_config.svh"

package expipe_pkg;

    /* Inlcude isnstruction macros */
    `include "instr_macros.svh"
    
    // Import global constants
    import len5_pkg::*;

    /* Add memory definitions */
    import memory_pkg::PPN_LEN;
    import memory_pkg::PADDR_LEN;
    import memory_pkg::PAGE_OFFSET_LEN;

    // ----
    // ROB
    // ----
    
    localparam ROB_IDX_LEN = $clog2(ROB_DEPTH);//3 // ROB index width
    localparam ROB_EXCEPT_LEN = 5;  // to fit the last four bits of the mcause/scause CSR and the fflags of the fcsr CSR

    typedef struct packed {
        logic                       valid;          // the ROB entry contains a valid instruction
        instr_t                     instruction;    // the instruction
        logic [XLEN-1:0]            instr_pc;       // the program counter if the instruction
        logic                       res_ready;      // the result of the instruction is ready
        logic [XLEN-1:0]            res_value;      // the value of the result (from the EU)
        logic [REG_IDX_LEN-1:0]     rd_idx;         // the destination register (rd)
        logic                       except_raised;  // an exception has been raised
        logic [ROB_EXCEPT_LEN-1:0]  except_code;    // the exception code
    } rob_entry_t;

    // ----
    // CDB
    // ----
    
    typedef struct packed {
        logic [ROB_IDX_LEN-1:0]     rob_idx;
        logic [XLEN-1:0]            value;
        logic                       except_raised;
        logic [ROB_EXCEPT_LEN-1:0]  except_code;
    } cdb_data_t;

    // ----------------
    // EXCEPTION CODES
    // ----------------
    // This are the LSBs of the entire exception codes defined by the specs. This are used in the execution pipeline to save area. This code can be directly appended when writing mcause/scause CSRs during exception handling
    typedef enum logic [ROB_EXCEPT_LEN-1:0] {
        E_I_ADDR_MISALIGNED   = 'h0,
        E_I_ACCESS_FAULT      = 'h1,
        E_ILLEGAL_INSTRUCTION = 'h2,
        E_BREAKPOINT          = 'h3,
        E_LD_ADDR_MISALIGNED  = 'h4,
        E_LD_ACCESS_FAULT     = 'h5,
        E_ST_ADDR_MISALIGNED  = 'h6,
        E_ST_ACCESS_FAULT     = 'h7,
        E_ENV_CALL_UMODE      = 'h8,
        E_ENV_CALL_SMODE      = 'h9,
        E_ENV_CALL_MMODE      = 'hb,
        E_INSTR_PAGE_FAULT    = 'hc,
        E_LD_PAGE_FAULT       = 'hd,
        E_ST_PAGE_FAULT       = 'hf,
        
        E_UNKNOWN             = 'ha    // reserved code 10, used for debugging
    } except_code_t;

    // -----------
    // ISSUE QUEUE
    // -----------
    localparam IQ_IDX_LEN = $clog2(IQ_DEPTH); // issue queue index width

    typedef struct packed {
        logic               valid; // The entry contains a valid instruction
        logic [XLEN-1:0]    curr_pc;
        logic [ILEN-1:0]    instruction;
        logic [XLEN-1:0]    pred_target;
        logic               pred_taken;
        logic               except_raised;
        except_code_t       except_code;
    } iq_entry_t;
    
    // ---------------
    // REGISTER STATUS
    // ---------------
    
    typedef struct packed {
        logic [ROB_IDX_LEN-1:0]     busy;       /* at most as many entry in the ROB, the current (this instruction) */
        logic [ROB_IDX_LEN-1:0]     rob_idx;
    } regstat_entry_t;

    // -----------
    // ISSUE LOGIC
    // -----------

    // IMMEDIATE TYPE
    typedef enum logic [2:0] {
        IMM_TYPE_I,
        IMM_TYPE_S,
        IMM_TYPE_B,
        IMM_TYPE_U,
        IMM_TYPE_J,
        IMM_TYPE_RS1
    } imm_format_t;

    // -------------------------
    // NUMBER OF EXECUTION UNITS
    // -------------------------

    localparam BASE_EU_N    = 5;   // load buffer, store buffer, branch unit, ALU, operands only

`ifdef LEN5_M_EN
    localparam MULT_EU_N    = 2;   // MULT, DIV
`else
    localparam MULT_EU_N    = 0;
`endif /* LEN5_M_EN */

`ifdef LEN5_FP_EN
    localparam FP_EU_N      = 1;     // FPU
`else
    localparam FP_EU_N      = 0;
`endif /* LEN5_FP_EN */

    // Total number of execution units
    localparam EU_N = BASE_EU_N + MULT_EU_N + FP_EU_N;

    // --------------------
    // RESERVATION STATIONS
    // --------------------

    // WIDTH OF THE CONTROL FIELDS IN THE DIFFERENT EUs
    // LOAD BUFFER
    localparam  LB_CTL_LEN      = 3;            // load type, see load buffer section below
    
    // STORE BUFFER
    localparam  SB_CTL_LEN      = LB_CTL_LEN;   // same type as load

    // BRANCH UNIT
    localparam  BU_CTL_LEN      = BRANCH_TYPE_LEN; // size of 'branch_type_t' from len5_pkg

    // ALU
    localparam  ALU_EXCEPT_LEN  = 2;
    localparam  ALU_CTL_LEN     = 4;            // ALU operation control

    // ALU opcodes
    typedef enum logic [ALU_CTL_LEN-1:0] {
        ALU_ADD,
        ALU_ADDW,
        ALU_SUB,
        ALU_SUBW,
        ALU_AND,
        ALU_OR,
        ALU_XOR,
        ALU_SLL,    // shift left
        ALU_SLLW,
        ALU_SRL,    // shift right
        ALU_SRLW,
        ALU_SRA,    // shift right w/ sign extension
        ALU_SRAW,
        ALU_SLT,    // set if less than
        ALU_SLTU    // set if less than (unsigned)
    } alu_ctl_t;

    // MULT
    localparam  MULT_EXCEPT_LEN = 2;
    localparam  MULT_CTL_LEN    = 3;            // integer multiplier operation control
    localparam  MULT_PIPE_DEPTH = 5;

    // Mult opcodes
    typedef enum logic [MULT_CTL_LEN-1:0] {
        MULT_MUL,
        MULT_MULW,
        MULT_MULH,
        MULT_MULHU,
        MULT_MULHSU
    } mult_ctl_t;

    // DIV
    localparam  DIV_EXCEPT_LEN  = 2;
    localparam  DIV_CTL_LEN     = 2;            // integer divider operation control

    // FPU
    localparam  FPU_EXCEPT_LEN  = 2;
    localparam  FPU_CTL_LEN     = 4;            // floating point multiplier operation control

    // OPERANDS ONLY
    localparam  OP_ONLY_CTL_LEN = 2;

    // MAXIMUM DIMENSION OF EU_CONTROL FIELDS
    localparam MAX_EU_CTL_LEN   = ALU_CTL_LEN;  // this must be set to the maximum of the previous parameters
    
    // ASSIGNED EU
    typedef enum logic [$clog2(EU_N)-1:0] {
        EU_LOAD_BUFFER,
        EU_STORE_BUFFER,
        EU_BRANCH_UNIT,
        EU_INT_ALU,
    `ifdef LEN5_M_EN
        EU_INT_MULT,
        EU_INT_DIV,
    `endif /* LEN5_M_EN */
    `ifdef LEN5_FP_EN
        EU_FPU,
    `endif /* LEN5_FP_EN */
        EU_OPERANDS_ONLY,   // probably not necessary if pipeline is stalled
        EU_NONE             //the instruction is directly sent to the ROB (csr, special instructions, etc.)
    } issue_eu_t;

    // ---------------
    // LOAD-STORE UNIT
    // ---------------
    localparam LDBUFF_IDX_LEN = $clog2(LDBUFF_DEPTH); //3 // load buffer address width
    localparam STBUFF_IDX_LEN = $clog2(STBUFF_DEPTH); //3 // store buffer address width
    localparam BUFF_IDX_LEN = (LDBUFF_IDX_LEN > STBUFF_IDX_LEN) ? (LDBUFF_IDX_LEN) : (STBUFF_IDX_LEN); // the largest of the two. Useful when comparing indexes from both
    localparam EXCEPT_TYPE_LEN = ROB_EXCEPT_LEN; // only the last four bits of the mcause/scause CSR
    localparam LDST_TYPE_LEN = LB_CTL_LEN; // 3 bits: 7 types of load (lb, lh, lw, ld, lbu, lhu, ldu), 4 types of store (sb, sh, sw and sd)
    typedef enum logic [LDST_TYPE_LEN-1:0] { 
        LS_BYTE,
        LS_BYTE_U,
        LS_HALFWORD,
        LS_HALFWORD_U,
        LS_WORD,
        LS_WORD_U,
        LS_DOUBLEWORD
    } ldst_type_t;
    
    // LOAD BUFFER ENTRY TYPE
    typedef struct packed {
        logic                       valid;             // the entry contains a valid instructions
        logic                       busy;              // The entry is waiting for an operation to complete
        logic                       store_dep;         // the entry must wait for alla previous store to commit before it can be executed
        logic                       pfwd_attempted;    // the entry is ready for the cache access
        `ifdef ENABLE_AGE_BASED_SELECTOR
        logic [ROB_IDX_LEN-1:0]     entry_age;         // the age of the entry, used for scheduling
        `endif
        logic [STBUFF_IDX_LEN:0]    older_stores;      // Number of older uncommitted stores (if 0, the entry is dependency-free)
        logic [LDST_TYPE_LEN-1:0]   load_type;         // LB, LBU, LH, LHU, LW, LWU, LD
        logic                       rs1_ready;         // the value of rs1 contained in 'rs1_value' field is valid
        logic [ROB_IDX_LEN-1:0]     rs1_idx;           // the index of the ROB that will contain the base address
        logic [XLEN-1:0]            rs1_value;         // the value of the base address
        logic [XLEN-1:0]            imm_value;         // the value of the immediate field (offset)
        logic                       vaddr_ready;       // the virtual address has already been computed
        logic [XLEN-1:0]            vaddr;             // the virtual address
        logic                       paddr_ready;       // the address translation (TLB access) has already completed
        logic [PPN_LEN-1:0]         ppn;  // the physical page number
        logic [ROB_IDX_LEN-1:0]     dest_idx;          // the entry of the ROB where the loaded value will be stored
        logic                       except_raised;
        except_code_t               except_code;       // exception code 
        logic [XLEN-1:0]            ld_value;          // the value loaded from memory
        logic                       completed;         // the value has been fetched from D$
    } lb_entry_t;

    // STORE BUFFER ENTRY TYPE
    typedef struct packed {
        logic                       valid;              // the entry contains a valid instructions
        logic                       busy;               // The entry is waiting for an operation to complete
        `ifdef ENABLE_AGE_BASED_SELECTOR
        logic [ROB_IDX_LEN-1:0]     entry_age;          // the age of the entry, used for scheduling
        `endif
        logic [LDST_TYPE_LEN-1:0]   store_type;         // SB, SH, SW, SD
        logic                       rs1_ready;          // the value of rs1 (BASE ADDRESS) contained in 'rs1_value' field is valid
        logic [ROB_IDX_LEN-1:0]     rs1_idx;            // the index of the ROB that will contain the base address
        logic [XLEN-1:0]            rs1_value;          // the value of the BASE ADDRESS
        logic                       rs2_ready;          // the value of rs2 (VALUE to be stored) contained in 'rs2_value' field is valid
        logic [ROB_IDX_LEN-1:0]     rs2_idx;            // the index of the ROB that will contain the base address
        logic [XLEN-1:0]            rs2_value;          // the value to be stored in memory
        logic [XLEN-1:0]            imm_value;          // the value of the immediate field (offset)
        logic                       vaddr_ready;        // the virtual address has already been computed
        logic [XLEN-1:0]            vaddr;              // the virtual address
        logic                       paddr_ready;        // the address translation (TLB access) has already completed
        logic [PPN_LEN-1:0]         ppn;                // the physical address (last 12 MSBs are identical to virtual address
        // logic                       dc_completed;       // the D$ completed the write request
        logic [ROB_IDX_LEN-1:0]     dest_idx;           // the entry of the ROB where the loaded value will be stored
        logic                       except_raised;
        except_code_t               except_code;        // exception code
        logic                       completed;          // the value has been stored to the D$
    } sb_entry_t;

    // ------------
    // COMMIT LOGIC
    // ------------

    // Virtual address adder exception codes
    typedef enum logic [1:0] { VADDER_ALIGN_EXCEPT, VADDER_PAGE_EXCEPT, VADDER_NO_EXCEPT } vadder_except_t;

    // Commit destination data type
    typedef enum logic [3:0] { 
        COMM_TYPE_NONE,     // no data to commit (e.g., nops)
        COMM_TYPE_INT_RF,   // commit to integer register file
        COMM_TYPE_FP_RF,    // commit to floating-point register file
        COMM_TYPE_STORE,    // commit store instructions
        COMM_TYPE_BRANCH,   // commit branch instructions
        COMM_TYPE_JUMP,     // commit jump-and-link instructions
        COMM_TYPE_CSR,      // commit to CSRs
        COMM_TYPE_FENCE,    // commit fence instructions
        COMM_TYPE_ECALL,    // commit ECALL instructions
        COMM_TYPE_EBREAK,   // commit EBREAK instructions
        COMM_TYPE_XRET,     // commit URET, SRET, and MRET instructions
        COMM_TYPE_WFI,      // commit wait for interrupt instructions
        COMM_TYPE_EXCEPT    // handle exceptions
    } comm_type_t;

endpackage

`endif
