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

// Opcode and CSR address definition
`include "instr_macros.svh"
`include "csr_macros.svh"

// Data types and parameters
import len5_pkg::XLEN;
import len5_pkg::FUNCT3_LEN;
import len5_pkg::REG_IDX_LEN;
import csr_pkg::*;
import expipe_pkg::ROB_EXCEPT_LEN;

module csrs (
    // Clock and reset 
    input   logic                       clk_i,
    input   logic                       rst_n_i,

    // Handshaking with commit logic
    input   logic                       valid_i,
    output  logic                       ready_o,

    // Control from commit logic
    input   csr_instr_t                 instr_type_i,
    input   logic [FUNCT3_LEN-1:0]      funct3_i,

    // CSR address and data to/from commit logic
    input   logic [CSR_ADDR_LEN-1:0]    addr_i,
    input   logic [REG_IDX_LEN-1:0]     rs1_idx_i,  // source register or unsigned immediate
    input   logic [XLEN-1:0]            rs1_data_i, // data to write to the CSR
    input   logic [ROB_EXCEPT_LEN-1:0]  exc_data_i, // exception data (e.g., FPU exceptions)
    input   logic [REG_IDX_LEN-1:0]     rd_idx_i,   // destination register
    output  logic [XLEN-1:0]            data_o,
    output  logic                       acc_exc_o   // ILLEGAL INSTRUCTION flag (invalid address or access permission)

    // Data to the FPU
    `ifdef LEN5_FP_EN
    ,
    output  logic [FCSR_FRM_LEN-1:0]    fpu_frm_o   // dynamic rounding mode
    `endif /* LEN5_FP_EN */
);

// CSR read value
logic   [XLEN-1:0]      csr_rd_val;

// 64-bit zero-extended immediate
logic   [XLEN-1:0]      uimm_zext   = { 59'b0, rs1_idx_i };

// CSR access exception
logic                   inv_acc_exc;    // invalid CSR address or no write permission
logic                   inv_op_exc;     // invalid operation (from funct3)

// ----
// CSRs
// ----

// Floating-point status
`ifdef LEN5_FP_EN
csr_fcsr_t      fcsr;
`endif /* LEN5_FP_EN */

// --------
// CSR READ
// --------

// Read the requested value if a valid request is received
always_comb begin : csr_read
    csr_rd_val      = '0;   // default value

    // Read the target CSR
    if (valid_i && instr_type_i == CSR_INSTR) begin
        // CSRRW, CSRRWI
        // -------------
        // Only read the CSR value if rd is not x0
        if ((funct3_i == `FUNCT3_CSRRW ||
             funct3_i == `FUNCT3_CSRRWI) &&
             rd_idx_i != '0) begin
            case (addr_i)
            `ifdef LEN5_FP_EN
                // fcsr
                `CSR_ADDR_FCSR:     csr_rd_val = { '0, fcsr };
                `CSR_ADDR_FRM:      csr_rd_val = { '0, fcsr.frm };
                `CSR_ADDR_FFLAGS:   csr_rd_val = { '0, fcsr.fflags };
            `endif /* LEN5_FP_EN */

                // Default
                default:;   // use default value (see Exception Handling)
            endcase

        // CSRRS, CSRRS, CSRRC, CSRRCI
        // ---------------------------
        // Read the CSR unconditionally 
        end else if (funct3_i == `FUNCT3_CSRRS ||
                     funct3_i == `FUNCT3_CSRRSI ||
                     funct3_i == `FUNCT3_CSRRC ||
                     funct3_i == `FUNCT3_CSRRCI) begin
            case (addr_i)
            `ifdef LEN5_FP_EN
                // fcsr
                `CSR_ADDR_FCSR:     csr_rd_val = { '0, fcsr };
                `CSR_ADDR_FRM:      csr_rd_val = { '0, fcsr.frm };
                `CSR_ADDR_FFLAGS:   csr_rd_val = { '0, fcsr.fflags };
            `endif /* LEN5_FP_EN */
                
                // Default
                default:;   // use default value (see Exception Handling)
            endcase
        end // else use the default value (see Exception Handling)
    end
end

// ---------
// CSR WRITE
// ---------

always_ff @( posedge clk_i or negedge rst_n_i ) begin : fcsr_reg
    if (!rst_n_i) begin
    `ifdef LEN5_FP_EN
        fcsr <= '0;
    `endif /* LEN5_FP_EN */
    end
    
    // Explicit CSR instructions
    else if (valid_i && instr_type_i == CSR_INSTR) begin
        case (addr_i)
            // FLOATING-POINT CSR
            // ------------------
        `ifdef LEN5_FP_EN
            `CSR_ADDR_FCSR: begin
                case (funct3_i)
                    `FUNCT3_CSRRW:  fcsr <= rs1_data_i[7:0];
                    `FUNCT3_CSRRS:  if (rs1_idx_i != '0) fcsr <= fcsr | rs1_data_i[7:0];
                    `FUNCT3_CSRRC:  if (rs1_idx_i != '0) fcsr <= fcsr & ~rs1_data_i[7:0]; 
                    `FUNCT3_CSRRWI: fcsr <= uimm_zext[7:0];
                    `FUNCT3_CSRRSI: if (rs1_idx_i != '0) fcsr <= fcsr | uimm_zext[7:0];
                    `FUNCT3_CSRRCI: if (rs1_idx_i != '0) fcsr <= fcsr & ~uimm_zext[7:0];
                    default:;   // do not modify the CSR value
                endcase
            end
            `CSR_ADDR_FRM: begin
                case (funct3_i)
                    `FUNCT3_CSRRW:  fcsr.frm <= rs1_data_i[2:0];
                    `FUNCT3_CSRRS:  if (rs1_idx_i != '0) fcsr.frm <= fcsr.frm | rs1_data_i[2:0];
                    `FUNCT3_CSRRC:  if (rs1_idx_i != '0) fcsr.frm <= fcsr.frm & ~rs1_data_i[2:0]; 
                    `FUNCT3_CSRRWI: fcsr.frm <= uimm_zext[2:0];
                    `FUNCT3_CSRRSI: if (rs1_idx_i != '0) fcsr.frm <= fcsr.frm | uimm_zext[2:0];
                    `FUNCT3_CSRRCI: if (rs1_idx_i != '0) fcsr.frm <= fcsr.frm & ~uimm_zext[2:0];
                    default:;   // do not modify the CSR value
                endcase
            end
            `CSR_ADDR_FFLAGS: begin
                case (funct3_i)
                    `FUNCT3_CSRRW:  fcsr.fflags <= rs1_data_i[4:0];
                    `FUNCT3_CSRRS:  if (rs1_idx_i != '0) fcsr.fflags <= fcsr.fflags | rs1_data_i[4:0];
                    `FUNCT3_CSRRC:  if (rs1_idx_i != '0) fcsr.fflags <= fcsr.fflags & ~rs1_data_i[4:0]; 
                    `FUNCT3_CSRRWI: fcsr.fflags <= uimm_zext[4:0];
                    `FUNCT3_CSRRSI: if (rs1_idx_i != '0) fcsr.fflags <= fcsr.fflags | uimm_zext[4:0];
                    `FUNCT3_CSRRCI: if (rs1_idx_i != '0) fcsr.fflags <= fcsr.fflags & ~uimm_zext[4:0];
                    default:;   // do not modify the CSR value
                endcase
            end
        `endif /* LEN5_FP_EN */
            default:;   // do not modify the CSR values
        endcase
    
    // FPU exceptions update
    end else if (valid_i && instr_type_i == FP_INSTR) begin
        fcsr.fflags <= exc_data_i[FCSR_FFLAGS_LEN-1:0];
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
            `CSR_ADDR_FCSR: inv_acc_exc = 1'b0; 
        `endif /* LEN5_FP_EN */
            
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
 * the current value of the selected CSR is updated on the first negative clock
 * edge, before the current value is modified.
 */

// CSR data
// --------
always_ff @( negedge clk_i or negedge rst_n_i ) begin : csr_out_reg
    if (!rst_n_i)   data_o <= '0;
    else            data_o <= csr_rd_val;
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
assign fpu_frm_o = fcsr.frm;
`endif /* LEN5_FP_EN */

endmodule