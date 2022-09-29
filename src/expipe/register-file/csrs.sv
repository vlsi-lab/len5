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
    input   csr_instr_t                 instr_type_i,
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
    output  logic [SATP_MODE_LEN-1:0]   vm_mode_o,

`ifdef LEN5_PRIVILEGED_EN
    // CSRs <--> issue logic
    output  logic                       mstatus_tsr_o,  // TSR bit from the mstatus CSR
`endif /* LEN5_PRIVILEGED_EN */

    // CSRs <--> memory system
    output  logic                       mem_vmem_on_o,
    output  logic                       mem_sum_bit_o,
    output  logic                       mem_mxr_bit_o,
    output  csr_priv_t                  mem_priv_mode_o,
    output  csr_priv_t                  mem_priv_mode_ls_o,
    output  asid_t                      mem_base_asid_o,
    output  logic [PPN_LEN-1:0]         mem_csr_root_ppn_o
);

// CSR read and write values
logic   [XLEN-1:0]      csr_rd_val;
logic   [XLEN-1:0]      csr_wr_val;

// 64-bit zero-extended immediate
logic   [XLEN-1:0]      uimm_zext;

// CSR access exception
logic                   inv_acc_exc;    // invalid CSR address or no write permission
logic                   inv_op_exc;     // invalid operation (from funct3)

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

// Floating-point status
`ifdef LEN5_FP_EN
csr_fcsr_t      fcsr;
`endif /* LEN5_FP_EN */

// SATP
csr_satp_t      satp;

// MSTATUS
csr_mstatus_t   mstatus;

// mstatus values
// --------------
// TODO: add proper write handling with CSR instructions
assign mstatus.sd            = 1'b0;
assign mstatus.not_used_4    = 'h0;
assign mstatus.sxl           = 'h0;
assign mstatus.uxl           = 'h0;
assign mstatus.not_used_3    = 'h0;
assign mstatus.tsr           = 1'b0;
assign mstatus.tw            = 1'b0;
assign mstatus.tvm           = 1'b0;
assign mstatus.mxr           = 1'b0;
assign mstatus.sum           = 1'b0;
assign mstatus.mprv          = 1'b0;
assign mstatus.xs            = 'h0;
assign mstatus.fs            = 'h0;
assign mstatus.mpp           = PRIV_MODE_S;
assign mstatus.not_used_2    = 'h0;
assign mstatus.spp           = PRIV_MODE_U;
assign mstatus.mpie          = 1'b0;
assign mstatus.not_used_1    = 'h0;
assign mstatus.spie          = 1'b0;
assign mstatus.upie          = 1'b0;
assign mstatus.mie           = 1'b0;
assign mstatus.not_used_0    = 1'b0;
assign mstatus.sie           = 1'b0;
assign mstatus.uie           = 1'b0;

assign uimm_zext             = { 59'b0, rs1_idx_i };

// MTVEC
csr_mtvec_t     mtvec;

// MEPC
csr_mepc_t      mepc;

// CSR write value MUX
// -------------------
always_comb begin : csr_wr_sel
    case (instr_type_i)
        CSR_CSRRWI, CSR_CSRRSI, CSR_CSRRCI:
            csr_wr_val  = uimm_zext;
        default: 
            csr_wr_val  = data_i;
    endcase
end

// --------
// CSR READ
// --------

// Read the requested value if a valid request is received
always_comb begin : csr_read
    csr_rd_val      = '0;   // default value

    // Read the target CSR
    if (valid_i) begin
        case (instr_type_i) begin
            // CSRRW, CSRRWI
            // -------------
            // Only read the CSR value if rd is not x0
            if ((funct3_i == `FUNCT3_CSRRW ||
                funct3_i == `FUNCT3_CSRRWI) &&
                rd_idx_i != '0) begin
                case (addr_i)

                    // Floating-point status CSR
                    // -------------------------
                `ifdef LEN5_FP_EN
                    // fcsr
                    `CSR_ADDR_FCSR:     csr_rd_val = { '0, fcsr };
                    `CSR_ADDR_FRM:      csr_rd_val = { '0, fcsr.frm };
                    `CSR_ADDR_FFLAGS:   csr_rd_val = { '0, fcsr.fflags };
                `endif /* LEN5_FP_EN */

                    // S-mode CSRs
                    // -----------
                    // satp
                    `CSR_ADDR_SATP: begin
                        // only readable in S and M modes
                        if (priv_mode >= PRIV_MODE_S)    csr_rd_val = satp;
                    end

                    // M-mode CSRs
                    // -----------
                    // mtvec
                    `CSR_ADDR_MTVEC: begin
                        csr_rd_val  = mtvec;
                    end
                    // mstatus
                    `CSR_ADDR_MSTATUS: begin
                        // Only readable in M mode
                        if (priv_mode >= PRIV_MODE_M)    csr_rd_val = mstatus;
                    end

                    // Default
                    default:;   // use default value (see Exception Handling)
                endcase

            // CSRRS, CSRRSI, CSRRC, CSRRCI
            // ----------------------------
            // Read the CSR unconditionally 
            end else if (funct3_i == `FUNCT3_CSRRS ||
                        funct3_i == `FUNCT3_CSRRSI ||
                        funct3_i == `FUNCT3_CSRRC ||
                        funct3_i == `FUNCT3_CSRRCI) begin
                case (addr_i)
                    // U-mode CSRs
                    // -----------
                `ifdef LEN5_FP_EN
                    // fcsr
                    `CSR_ADDR_FCSR:     csr_rd_val = { '0, fcsr };
                    `CSR_ADDR_FRM:      csr_rd_val = { '0, fcsr.frm };
                    `CSR_ADDR_FFLAGS:   csr_rd_val = { '0, fcsr.fflags };
                `endif /* LEN5_FP_EN */
                    
                    // S-mode CSRs
                    // -----------
                    // satp
                    `CSR_ADDR_SATP: begin
                        // only readable in S and M modes
                        if (priv_mode >= PRIV_MODE_S)    csr_rd_val = satp;
                    end

                    // M-mode CSRs
                    // -----------
                    // mtvec
                    `CSR_ADDR_MTVEC: begin
                        if (priv_mode >= PRIV_MODE_M) csr_rd_val = mtvec;
                    end
                    // mstatus
                    `CSR_ADDR_MSTATUS: begin
                        if (priv_mode >= PRIV_MODE_M) csr_rd_val = mstatus;
                    end
                    // MEPC
                    `CSR_ADDR_MEPC: begin
                        if (priv_mode >= PRIV_MODE_M) csr_rd_val = mepc;
                    end
                    
                    // Default
                    default:;   // use default value (see Exception Handling)
                endcase
            end // else use the default value (see Exception Handling)
        end
    end
end

// ---------
// CSR WRITE
// ---------

always_ff @( posedge clk_i or negedge rst_n_i ) begin : fcsr_reg
    if (!rst_n_i) begin
        // priv mode
        priv_mode   <= PRIV_MODE_M;

    `ifdef LEN5_FP_EN
        // fcsr
        fcsr        <= '0;
    `endif /* LEN5_FP_EN */

        // satp
        // The following line resets sapt MODE, ASID, and PPN (physical page 
        // number of the root page table) to BARE (no virtual memory), 0x00, 
        // and 0x00 respectively. Subsequent instructions are required to
        // enable VM and point to a proper page table. 
        satp.mode   <= `BOOT_VM_MODE;
        satp.asid   <= '0;
        satp.ppn    <= '0;

        // mtvec
        mtvec       <= 'h0;

        // MEPC
        mepc        <= 'h0;
    end
    
    // Explicit CSR instructions
    else if (valid_i && instr_type_i == CSR_INSTR) begin
        case (addr_i)
            // FLOATING-POINT CSR
            // ------------------
        `ifdef LEN5_FP_EN
            `CSR_ADDR_FCSR: begin
                case (funct3_i)
                    `FUNCT3_CSRRW:  fcsr <= data_i[7:0];
                    `FUNCT3_CSRRS:  if (rs1_idx_i != '0) fcsr <= fcsr | data_i[7:0];
                    `FUNCT3_CSRRC:  if (rs1_idx_i != '0) fcsr <= fcsr & ~data_i[7:0]; 
                    `FUNCT3_CSRRWI: fcsr <= uimm_zext[7:0];
                    `FUNCT3_CSRRSI: if (rs1_idx_i != '0) fcsr <= fcsr | uimm_zext[7:0];
                    `FUNCT3_CSRRCI: if (rs1_idx_i != '0) fcsr <= fcsr & ~uimm_zext[7:0];
                    default:;   // do not modify the CSR value
                endcase
            end
            `CSR_ADDR_FRM: begin
                case (funct3_i)
                    `FUNCT3_CSRRW:  fcsr.frm <= data_i[2:0];
                    `FUNCT3_CSRRS:  if (rs1_idx_i != '0) fcsr.frm <= fcsr.frm | data_i[2:0];
                    `FUNCT3_CSRRC:  if (rs1_idx_i != '0) fcsr.frm <= fcsr.frm & ~data_i[2:0]; 
                    `FUNCT3_CSRRWI: fcsr.frm <= uimm_zext[2:0];
                    `FUNCT3_CSRRSI: if (rs1_idx_i != '0) fcsr.frm <= fcsr.frm | uimm_zext[2:0];
                    `FUNCT3_CSRRCI: if (rs1_idx_i != '0) fcsr.frm <= fcsr.frm & ~uimm_zext[2:0];
                    default:;   // do not modify the CSR value
                endcase
            end
            `CSR_ADDR_FFLAGS: begin
                case (funct3_i)
                    `FUNCT3_CSRRW:  fcsr.fflags <= data_i[4:0];
                    `FUNCT3_CSRRS:  if (rs1_idx_i != '0) fcsr.fflags <= fcsr.fflags | data_i[4:0];
                    `FUNCT3_CSRRC:  if (rs1_idx_i != '0) fcsr.fflags <= fcsr.fflags & ~data_i[4:0]; 
                    `FUNCT3_CSRRWI: fcsr.fflags <= uimm_zext[4:0];
                    `FUNCT3_CSRRSI: if (rs1_idx_i != '0) fcsr.fflags <= fcsr.fflags | uimm_zext[4:0];
                    `FUNCT3_CSRRCI: if (rs1_idx_i != '0) fcsr.fflags <= fcsr.fflags & ~uimm_zext[4:0];
                    default:;   // do not modify the CSR value
                endcase
            end
        `endif /* LEN5_FP_EN */

            // S-MODE CSRs
            // -----------

            // satp
            `CSR_ADDR_SATP: begin
                case (funct3_i)
                    `FUNCT3_CSRRW:  begin
                        if (priv_mode >= PRIV_MODE_S) begin
                            if (data_i[63:60] == BARE ||
                                data_i[63:60] == SV39 ||
                                data_i[63:60] == SV48) begin
                                satp.mode   <= data_i[63:60];
                            end
                            satp.asid   <= data_i[59:44];
                            satp.ppn    <= data_i[43:0];
                        end
                    end
                    `FUNCT3_CSRRS:  begin
                        if (priv_mode >= PRIV_MODE_S) begin
                            if (data_i[63:60] == BARE ||
                                data_i[63:60] == SV39 ||
                                data_i[63:60] == SV48) begin
                                satp.mode   <= satp.mode | data_i[63:60];
                            end
                            satp.asid   <= satp.asid | data_i[59:44];
                            satp.ppn    <= satp.ppn | data_i[43:0];
                        end
                    end
                    `FUNCT3_CSRRC:  begin
                        if (priv_mode >= PRIV_MODE_S) begin
                            if (data_i[63:60] == BARE ||
                                data_i[63:60] == SV39 ||
                                data_i[63:60] == SV48) begin
                                satp.mode   <= satp.mode & ~data_i[63:60];
                            end
                            satp.asid   <= satp.asid & ~data_i[59:44];
                            satp.ppn    <= satp.ppn & ~data_i[43:0];
                        end
                    end
                    `FUNCT3_CSRRWI: begin
                        if (priv_mode >= PRIV_MODE_S) begin
                            if (uimm_zext[63:60] == BARE ||
                                uimm_zext[63:60] == SV39 ||
                                uimm_zext[63:60] == SV48) begin
                                satp.mode   <= uimm_zext[63:60];
                            end
                            satp.asid   <= uimm_zext[59:44];
                            satp.ppn    <= uimm_zext[43:0];
                        end
                    end
                    `FUNCT3_CSRRSI: begin
                        if (priv_mode >= PRIV_MODE_S) begin
                            if (uimm_zext[63:60] == BARE ||
                                uimm_zext[63:60] == SV39 ||
                                uimm_zext[63:60] == SV48) begin
                                satp.mode   <= satp.mode | uimm_zext[63:60];
                            end
                            satp.asid   <= satp.asid | uimm_zext[59:44];
                            satp.ppn    <= satp.ppn | uimm_zext[43:0];
                        end
                    end
                    `FUNCT3_CSRRCI: begin
                        if (priv_mode >= PRIV_MODE_S) begin
                            if (uimm_zext[63:60] == BARE ||
                                uimm_zext[63:60] == SV39 ||
                                uimm_zext[63:60] == SV48) begin
                                satp.mode   <= satp.mode & ~uimm_zext[63:60];
                            end
                            satp.asid   <= satp.asid & ~uimm_zext[59:44];
                            satp.ppn    <= satp.ppn & ~uimm_zext[43:0];
                        end
                    end
                    default:;   // do not modify the CSR value
                endcase
            end

            // M-mode CSRs
            // -----------
            // mtvec
            `CSR_ADDR_MTVEC: begin
                if (priv_mode >= PRIV_MODE_M) begin
                    case (funct3_i)
                        `FUNCT3_CSRRW:  mtvec <= data_i;
                        `FUNCT3_CSRRS:  if (rs1_idx_i != '0) mtvec <= mtvec | data_i;
                        `FUNCT3_CSRRC:  if (rs1_idx_i != '0) mtvec <= mtvec & ~data_i; 
                        `FUNCT3_CSRRWI: mtvec <= uimm_zext;
                        `FUNCT3_CSRRSI: if (rs1_idx_i != '0) mtvec <= mtvec | uimm_zext;
                        `FUNCT3_CSRRCI: if (rs1_idx_i != '0) mtvec <= mtvec & ~uimm_zext; 
                        default:;
                    endcase
                end
            end

            // MEPC
            `CSR_ADDR_MEPC: begin
                if (priv_mode >= PRIV_MODE_M) begin
                    case (funct3_i)
                        `FUNCT3_CSRRW:  mepc <= data_i;
                        `FUNCT3_CSRRS:  if (rs1_idx_i != '0) mepc <= mepc | data_i;
                        `FUNCT3_CSRRC:  if (rs1_idx_i != '0) mepc <= mepc & ~data_i; 
                        `FUNCT3_CSRRWI: mepc <= uimm_zext;
                        `FUNCT3_CSRRSI: if (rs1_idx_i != '0) mepc <= mepc | uimm_zext;
                        `FUNCT3_CSRRCI: if (rs1_idx_i != '0) mepc <= mepc & ~uimm_zext; 
                        default:;
                    endcase
                end
            end

            default:;   // do not modify the CSR values
        endcase
    
    // FPU exceptions update
`ifdef LEN5_FP_EN
    end else if (valid_i && instr_type_i == CSR_FP_INSTR) begin
        fcsr.fflags <= exc_data_i[FCSR_FFLAGS_LEN-1:0];
`endif /* LEN5_FP_EN */
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

// Data to the issue logic
`ifdef LEN5_PRIVILEGED_EN
assign  mstatus_tsr_o   = mstatus.tsr;
`endif /* LEN5_PRIVILEGED_EN */

// Data to commit logic
assign  mtvec_o         = mtvec;

// Memory protection mode
assign  vm_mode_o       = satp.mode;

// Data to the memory system
assign  mem_vmem_on_o       = (satp.mode != BARE) ? 1'b1 : 1'b0;
assign  mem_sum_bit_o       = mstatus.sum;
assign  mem_mxr_bit_o       = mstatus.mxr;
assign  mem_priv_mode_o     = priv_mode;
assign  mem_priv_mode_ls_o  = (mstatus.mprv) ? PRIV_MODE_M : priv_mode;
assign  mem_base_asid_o     = satp.asid;
assign  mem_csr_root_ppn_o  = satp.ppn;

endmodule