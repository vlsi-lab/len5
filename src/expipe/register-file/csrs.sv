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
// File: csrs.sv
// Author: Michele Caon
// Date: 03/11/2021

// LEN5 compilation switches
`include "len5_config.svh"

// Opcode and CSR address definition
`include "instr_macros.svh"
`include "csr_macros.svh"

// Data types and parameters
import len5_pkg::*;
import csr_pkg::*;
import expipe_pkg::*;
import memory_pkg::PPN_LEN;
import memory_pkg::asid_t;

module csrs (
    // Clock and reset 
    input   logic                       clk_i,
    input   logic                       rst_n_i,

    // Handshaking with commit logic
    input   logic                       valid_i,

    // Control from commit logic
    input   comm_csr_instr_t            comm_insn_i,    // committing instruction type
    input   csr_op_t                    comm_op_i,
    input   logic [FUNCT3_LEN-1:0]      funct3_i,

    // CSR address and data to/from commit logic
    input   logic [CSR_ADDR_LEN-1:0]    addr_i,
    input   logic [REG_IDX_LEN-1:0]     rs1_idx_i,  // source register or unsigned immediate
    input   logic [XLEN-1:0]            data_i,     // data to write to the CSR
    input   except_code_t               exc_data_i, // exception data (e.g., FPU exceptions)
    input   logic [REG_IDX_LEN-1:0]     rd_idx_i,   // destination register
    output  csr_t                       data_o,
    output  logic                       acc_exc_o,  // ILLEGAL INSTRUCTION flag (invalid address or access permission)
    output  csr_mtvec_t                 mtvec_o,    // exception base address and mode

    // Data to the FPU
    `ifdef LEN5_FP_EN
    output  logic [FCSR_FRM_LEN-1:0]    fpu_frm_o,  // dynamic rounding mode
    `endif /* LEN5_FP_EN */

    // Data to the load/store unit
    output  csr_priv_t                  priv_mode_o     // current privilege mode
);

// CSR read and write values and control
logic                   csr_rd_en;
logic                   csr_wr_en;
logic   [XLEN-1:0]      csr_rd_val;
logic   [XLEN-1:0]      csr_wr_val;

// 64-bit zero-extended immediate
logic   [XLEN-1:0]      uimm_zext;

// CSR access exception
logic                   inv_acc_exc;    // invalid CSR address or no write permission
logic                   inv_op_exc;     // invalid operation (from funct3)

// Performance counters control
logic                   mcycle_load;
logic                   minstret_load;
`ifdef LEN5_CSR_HPMCOUNTERS_EN
logic                   hpmcounter3_load;
logic                   hpmcounter4_load;
logic                   hpmcounter5_load;
logic                   hpmcounter6_load;
`endif /* LEN5_CSR_HPMCOUNTERS_EN */

// ------------------------
// PROCESSOR EXECUTION MODE
// ------------------------
// NOTE: code should not be able to discover the mode it is running in, so the
// following CSR is only visible by the core itself. At reset, the execution 
// mode defaults to M-mode.
csr_priv_t              priv_mode;      // current execution mode

// ----
// CSRs
// ----

// Machine-mode CSRs
// -----------------
// MISA
csr_misa_t          misa;
// Implementation IDs
csr_mvendorid_t     mvendorid;
csr_marchid_t       marchid;
csr_mimpid_t        mimpid;
csr_mhartid_t       mhartid;
// MSTATUS
csr_mstatus_t       mstatus;
// MTVEC
csr_mtvec_t         mtvec;
// Performance counters
csr_mcycle_t        mcycle;
csr_minstret_t      minstret;
csr_mcounteren_t    mcounteren;
csr_mcountinhibit_t mcountinhibit;
`ifdef LEN5_CSR_HPMCOUNTERS_EN
csr_hpmcounter_t    hpmcounter3;    // counts retired jump instr
csr_hpmcounter_t    hpmcounter4;    // counts retired branch instr
csr_hpmcounter_t    hpmcounter5;    // counts retired load instr
csr_hpmcounter_t    hpmcounter6;    // counts retired store instr
`endif /* LEN5_CSR_HPMCOUNTERS_EN */
// MSCRATCH
csr_mscratch_t      mscratch;
// MEPC
csr_mepc_t          mepc;
// MCAUSE
csr_mcause_t        mcause;
// MTVAL
csr_mtval_t         mtval;

// -----------
// CSR CONTROL
// -----------

// CSR read-write control
// ----------------------
always_comb begin : csr_rdwr_ctl
    csr_rd_en       = 1'b0;
    csr_wr_en       = 1'b0;
    unique case (comm_op_i)
        CSR_OP_CSRRW, CSR_OP_CSRRWI: begin
            csr_rd_en   = valid_i & (rd_idx_i != 0);
            csr_wr_en   = valid_i;
        end
        CSR_OP_CSRRS, CSR_OP_CSRRC, CSR_OP_CSRRC, CSR_OP_CSRRCI: begin
            csr_rd_en   = valid_i;
            csr_wr_en   = valid_i & (rs1_idx_i != 0);
        end
        CSR_OP_SYSTEM, CSR_OP_SYSTEM: begin
            csr_wr_en   = 1'b1; // write CSR unconditionally
        end
        default:; // use default values
    endcase
end

// CSR write value MUX
// -------------------
assign  uimm_zext   = { 59'b0, rs1_idx_i };
always_comb begin : csr_wr_sel
    unique case (comm_op_i)
        CSR_OP_CSRRWI: csr_wr_val  = uimm_zext;
        CSR_OP_CSRRS:  csr_wr_val  = csr_rd_val | data_i;
        CSR_OP_CSRRSI: csr_wr_val  = csr_rd_val | uimm_zext;
        CSR_OP_CSRRC:  csr_wr_val  = csr_rd_val & ~data_i;
        CSR_OP_CSRRCI: csr_wr_val  = csr_rd_val & ~uimm_zext;
        default:       csr_wr_val  = data_i;
    endcase
end

// --------------
// HARDWIRED CSRs
// --------------

// MISA
assign  misa.mxl        = 2'b10;    // 64-bit base ISA
assign  misa.not_used   = 'h0;
assign  misa.extensions = `MISA_EXT;

// Implementation IDs
assign  mvendorid       = `CSR_MVENDORID;
assign  marchid         = `CSR_MARCHID;
assign  mimpid          = `CSR_MIMPID;
assign  mhartid         = `CSR_MHARTID;

// MSTATUS
assign  mstatus.sd           = 1'b0;
assign  mstatus.not_used_4   = 'h0;
assign  mstatus.sxl          = 'h0;
assign  mstatus.uxl          = 'h0;
assign  mstatus.not_used_3   = 'h0;
assign  mstatus.tsr          = 1'b0;
assign  mstatus.tw           = 1'b0;
assign  mstatus.tvm          = 1'b0;
assign  mstatus.mxr          = 1'b0;
assign  mstatus.sum          = 1'b0;
assign  mstatus.mprv         = 1'b0;
assign  mstatus.xs           = 'h0;
assign  mstatus.fs           = 'h0;
// assign mstatus.mpp           = PRIV_MODE_U;
assign  mstatus.not_used_2   = 'h0;
assign  mstatus.spp          = 'h0;     // S-mode not supported
// assign mstatus.mpie          = 1'b0;
assign  mstatus.not_used_1   = 'h0;
assign  mstatus.spie         = 1'b0;
assign  mstatus.upie         = 1'b0;
// assign mstatus.mie           = 1'b0;
assign  mstatus.not_used_0   = 1'b0;
assign  mstatus.sie          = 1'b0;
assign  mstatus.uie          = 1'b0;

// MCOUNTEREN
// NOTE: all counters accessible (even if not implemented)
assign  mcounteren           = {32{1'b1}};

// MCOUNTINHIBIT
// NOTE: only mcycle, minstret, and hpmcounter3/4 are enabled
`ifdef LEN5_CSR_HPMCOUNTERS_EN
assign  mcountinhibit        = {{25{1'b1}}, 7'b0000000};
`else
assign  mcountinhibit        = {{29{1'b1}}, 3'b000};
`endif /* LEN5_CSR_HPMCOUNTERS_EN */

// --------
// CSR READ
// --------

// Read the requested value if a valid request is received
always_comb begin : csr_read
    csr_rd_val      = '0;   // default value

    // Read the target CSR
    if (csr_rd_en)  begin
        unique case (addr_i)
            // M-MODE CSRs
            // -----------
            // misa
            `CSR_ADDR_MISA: begin
                if (priv_mode >= PRIV_MODE_M)   csr_rd_val  = misa;
            end
            // mvendorid
            `CSR_ADDR_MVENDORID: begin
                if (priv_mode >= PRIV_MODE_M)   csr_rd_val  = mvendorid;
            end
            // marchid
            `CSR_ADDR_MARCHID: begin
                if (priv_mode >= PRIV_MODE_M)   csr_rd_val  = marchid;
            end
            // mimpid
            `CSR_ADDR_MIMPID: begin
                if (priv_mode >= PRIV_MODE_M)   csr_rd_val  = mimpid;
            end
            // mhartid
            `CSR_ADDR_MHARTID: begin
                if (priv_mode >= PRIV_MODE_M)   csr_rd_val  = mhartid;
            end
            // mstatus
            `CSR_ADDR_MSTATUS: begin
                if (priv_mode >= PRIV_MODE_M)   csr_rd_val  = mstatus;
            end
            // mtvec
            `CSR_ADDR_MTVEC: begin
                if (priv_mode >= PRIV_MODE_M)   csr_rd_val  = mtvec;
            end
            // Performance counters (also accessible in user-mode)
            `CSR_ADDR_MCYCLE: begin
                csr_rd_val  = mcycle;
            end
            `CSR_ADDR_MINSTRET: begin
                csr_rd_val  = minstret;
            end
        `ifdef LEN5_CSR_HPMCOUNTERS_EN
            `CSR_ADDR_HPMCOUNTER3: begin
                csr_rd_val  = hpmcounter3;
            end
            `CSR_ADDR_HPMCOUNTER4: begin
                csr_rd_val  = hpmcounter4;
            end
            `CSR_ADDR_HPMCOUNTER5: begin
                csr_rd_val  = hpmcounter5;
            end
            `CSR_ADDR_HPMCOUNTER6: begin
                csr_rd_val  = hpmcounter6;
            end
        `endif /* LEN5_CSR_HPMCOUNTERS_EN */
            `CSR_ADDR_MCOUNTEREN: begin
                csr_rd_val  = mcounteren;
            end
            `CSR_ADDR_MSCRATCH: begin
                if (priv_mode >= PRIV_MODE_M)   csr_rd_val  = mscratch;
            end
            `CSR_ADDR_MEPC: begin
                if (priv_mode >= PRIV_MODE_M)   csr_rd_val  = mepc;
            end
            `CSR_ADDR_MCAUSE: begin
                if (priv_mode >= PRIV_MODE_M)   csr_rd_val  = mcause;
            end
            `CSR_ADDR_MTVAL: begin
                if (priv_mode >= PRIV_MODE_M)   csr_rd_val  = mtval;
            end
            default:; // use default read value
        endcase
    end
end

// ---------
// CSR WRITE
// ---------

always_ff @( posedge clk_i or negedge rst_n_i ) begin : fcsr_reg
    if (!rst_n_i) begin
        // CSR DEFAULT VALUES
        // ------------------

        // priv mode
        priv_mode       <= PRIV_MODE_M;

    `ifdef LEN5_FP_EN
        // fcsr
        fcsr            <= '0;
    `endif /* LEN5_FP_EN */
        // mstatus
        mstatus.mpp     <= PRIV_MODE_U;
        mstatus.mpie    <= 1'b0;
        mstatus.mie     <= 1'b0;
        // mtvec
        mtvec.base      <= `CSR_MTVEC_BASE;
        mtvec.mode      <= `CSR_MTVEC_MODE;
        // mscratch
        mscratch        <= 'h0;
        // mepc
        mepc            <= 'h0;
        // mcause
        mcause          <= 'h0;
        // mtval
        mtval           <= 'h0;

    end else if (csr_wr_en) begin
        // CSR EXPLICIT WRITE
        // ------------------
        unique case (addr_i)
            // M-MODE CSRs
            // -----------
            // mstatus
            `CSR_ADDR_MSTATUS: begin
                if (priv_mode >= PRIV_MODE_M) begin
                    mstatus.mpp     <= csr_wr_val[12:11];
                    mstatus.mpie    <= csr_wr_val[7];
                    mstatus.mie     <= csr_wr_val[3];
                end
            end
            // mtvec
            `CSR_ADDR_MTVEC: begin
                if (priv_mode >= PRIV_MODE_M)   mtvec       <= csr_wr_val;
            end
            // mscratch
            `CSR_ADDR_MSCRATCH: begin
                if (priv_mode >= PRIV_MODE_M)   mscratch    <= csr_wr_val;
            end
            // mepc
            `CSR_ADDR_MEPC: begin
            `ifdef LEN5_C_EN
                if (comm_op_i == CSR_OP_SYSTEM || priv_mode >= PRIV_MODE_M)   
                    mepc    <= csr_wr_val & ~('h01);
            `else
                if (comm_op_i == CSR_OP_SYSTEM || priv_mode >= PRIV_MODE_M)   
                    mepc    <= csr_wr_val & ~('h03);
            `endif /* LEN5_C_EN */
            end
            // mcause
            `CSR_ADDR_MCAUSE: begin
                if (comm_op_i == CSR_OP_SYSTEM || priv_mode >= PRIV_MODE_M)
                    mcause  <= csr_wr_val;
            end
            // mtval 
            `CSR_ADDR_MTVAL: begin
                if (comm_op_i == CSR_OP_SYSTEM || priv_mode >= PRIV_MODE_M)
                    mtval   <= csr_wr_val;
            end
            default:; // do not modify CSRs
        endcase
    end
end

// Performance counters
// --------------------
// Control
always_comb begin : perf_counters_ctl
    mcycle_load         = 1'b0;
    minstret_load       = 1'b0;
`ifdef LEN5_CSR_HPMCOUNTERS_EN
    hpmcounter3_load    = 1'b0;
    hpmcounter4_load    = 1'b0;
    hpmcounter5_load    = 1'b0;
    hpmcounter6_load    = 1'b0;
`endif /* LEN5_CSR_HPMCOUNTERS_EN */
    if (csr_wr_en) begin
        unique case (addr_i)
            `CSR_ADDR_MCYCLE:       mcycle_load         = 1'b1;
            `CSR_ADDR_MINSTRET:     minstret_load       = 1'b1;
        `ifdef LEN5_CSR_HPMCOUNTERS_EN
            `CSR_ADDR_HPMCOUNTER3:  hpmcounter3_load    = 1'b1;
            `CSR_ADDR_HPMCOUNTER4:  hpmcounter4_load    = 1'b1;
            `CSR_ADDR_HPMCOUNTER5:  hpmcounter5_load    = 1'b1;
            `CSR_ADDR_HPMCOUNTER6:  hpmcounter6_load    = 1'b1;
        `endif /* LEN5_CSR_HPMCOUNTERS_EN */
            default:;
        endcase
    end
end
// Counters
always_ff @( posedge clk_i or negedge rst_n_i ) begin : perf_counters
    if (!rst_n_i) begin
        mcycle      <= 'h0;
        minstret    <= 'h0;
    `ifdef LEN5_CSR_HPMCOUNTERS_EN
        hpmcounter3 <= 'h0;
        hpmcounter4 <= 'h0;
        hpmcounter5 <= 'h0;
        hpmcounter6 <= 'h0;
    `endif /* LEN5_CSR_HPMCOUNTERS_EN */
    end else begin
        // mcycle
        if (mcycle_load)
            mcycle      <= csr_wr_val;
        else if (!mcountinhibit[0])
            mcycle      <= mcycle + 1;
        // minstret
        if (minstret_load)
            minstret    <= csr_wr_val;
        else if (comm_insn_i != COMM_CSR_INSTR_TYPE_NONE && !mcountinhibit[2])
            minstret    <= minstret + 1;
    `ifdef LEN5_CSR_HPMCOUNTERS_EN
        // hpmcounter3 (retired jumps)
        if (hpmcounter3_load)
            hpmcounter3 <= csr_wr_val;
        else if (comm_insn_i == COMM_CSR_INSTR_TYPE_JUMP && !mcountinhibit[3])
            hpmcounter3 <= hpmcounter3 + 1;
        // hpmcounter4 (retired branches)
        if (hpmcounter4_load)
            hpmcounter4 <= csr_wr_val;
        else if (comm_insn_i == COMM_CSR_INSTR_TYPE_BRANCH && !mcountinhibit[4])
            hpmcounter4 <= hpmcounter4 + 1;
        // hpmcounter5 (retired loads)
        if (hpmcounter5_load)
            hpmcounter5 <= csr_wr_val;
        else if (comm_insn_i == COMM_CSR_INSTR_TYPE_LOAD && !mcountinhibit[5])
            hpmcounter5 <= hpmcounter5 + 1;
        // hpmcounter6 (retired stores)
        if (hpmcounter6_load)
            hpmcounter6 <= csr_wr_val;
        else if (comm_insn_i == COMM_CSR_INSTR_TYPE_STORE && !mcountinhibit[6])
            hpmcounter6 <= hpmcounter6 + 1;
    `endif /* LEN5_CSR_HPMCOUNTERS_EN */
    end
end

// ------------------
// EXCEPTION HANDLING
// ------------------

// Invalid opcode
always_comb begin : exc_handling
    if (valid_i) begin
        case (funct3_i)
            `FUNCT3_CSRRW,
            `FUNCT3_CSRRS,
            `FUNCT3_CSRRC,
            `FUNCT3_CSRRWI, 
            `FUNCT3_CSRRSI,
            `FUNCT3_CSRRCI: inv_op_exc = 1'b0;

            default:        inv_op_exc = 1'b1;
        endcase
    end else    inv_op_exc = 1'b0;

    // Invalid access (CSR address or no write permission)
    if (valid_i) begin
        case (addr_i)
            // fcsr (no access restrictions)
        `ifdef LEN5_FP_EN
            `CSR_ADDR_FFLAGS,
            `CSR_ADDR_FRM,
            `CSR_ADDR_FCSR, 
        `endif /* LEN5_FP_EN */
            `CSR_ADDR_SATP,
            `CSR_ADDR_MTVEC: inv_acc_exc = 1'b0;
            
            // Invalid address
            default:        inv_acc_exc = 1'b1;
        endcase
    end else    inv_acc_exc = 1'b0;
end

// ----------------
// OUTPUT REGISTERS
// ----------------

/*
 * NOTE: CSRs are accessed in a single read-modify-write operation. Therefore,
 * the current value of the selected CSR is accessed on the first negative clock
 * edge, before the current value is modified.
 */

// CSR data
// --------
always_ff @( negedge clk_i or negedge rst_n_i ) begin : csr_out_reg
    if (!rst_n_i)       data_o <= '0;
    else                data_o <= csr_rd_val;
end

// CSR access exception
// --------------------
always_ff @( negedge clk_i or negedge rst_n_i ) begin : csr_exc_reg
    if (!rst_n_i)       acc_exc_o <= 1'b0;
    else if (valid_i)   acc_exc_o <= inv_acc_exc | inv_op_exc;
end

// -----------
// OUTPUT DATA
// -----------

// Data to FPU
`ifdef LEN5_FP_EN
assign  fpu_frm_o       = fcsr.frm;
`endif /* LEN5_FP_EN */

assign  priv_mode_o     = priv_mode;

// Data to commit logic
assign  mtvec_o         = mtvec;

endmodule