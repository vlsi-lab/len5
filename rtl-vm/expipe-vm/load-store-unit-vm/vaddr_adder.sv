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
// File: vaddr_adder.sv
// Author: Michele Caon
// Date: 29/10/2019

import len5_pkg::XLEN;
import expipe_pkg::*;

import csr_pkg::satp_mode_t;
import csr_pkg::SATP_MODE_LEN;
import csr_pkg::BARE;
import csr_pkg::SV39;
import csr_pkg::SV48;

module vaddr_adder #(
    IDX_LEN = 8
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,

    // Virtual memory configuration
    input logic [SATP_MODE_LEN-1:0] vm_mode_i,  // virtual memory MODE (from the 'satp' CSR)

    // Handshake from/to the load/store buffers
    input  logic lsb_valid_i,
    input  logic lsb_ready_i,
    output logic lsb_valid_o,
    output logic lsb_ready_o,

    // Data from/to the load/store buffers
    input  logic                             is_store_i,
    input  logic         [         XLEN-1:0] rs1_value_i,
    input  logic         [         XLEN-1:0] imm_value_i,
    input  logic         [      IDX_LEN-1:0] lsb_idx_i,
    input  logic         [LDST_TYPE_LEN-1:0] ldst_type_i,
    output logic                             is_store_o,
    output logic         [         XLEN-1:0] vaddr_o,
    output logic         [      IDX_LEN-1:0] lsb_idx_o,
    output except_code_t                     except_o
);

  // DEFINITIONS
  logic [         XLEN-1:0] rs1_value;
  logic [         XLEN-1:0] imm_value;
  logic [LDST_TYPE_LEN-1:0] ldst_type;
  logic [SATP_MODE_LEN-1:0] vm_mode;
  logic align_except, pfault_except;

  // ---------------
  // INPUT REGISTERS
  // ---------------
  always_ff @(posedge clk_i or negedge rst_n_i) begin : input_registers
    if (!rst_n_i) begin
      is_store_o  <= 1'b0;
      rs1_value   <= 'd0;
      imm_value   <= 'd0;
      vm_mode     <= BARE;
      ldst_type   <= LS_DOUBLEWORD;
      lsb_idx_o   <= 'd0;
      lsb_valid_o <= 'd0;
    end else if (flush_i) begin
      is_store_o  <= 1'b0;
      rs1_value   <= 'd0;
      imm_value   <= 'd0;
      vm_mode     <= BARE;
      ldst_type   <= LS_DOUBLEWORD;
      lsb_idx_o   <= 'd0;
      lsb_valid_o <= 'd0;
    end else if (lsb_ready_i) begin  /* only proceed if the LSB is ready */
      is_store_o  <= is_store_i;
      rs1_value   <= rs1_value_i;
      imm_value   <= imm_value_i;
      vm_mode     <= vm_mode_i;
      lsb_idx_o   <= lsb_idx_i;
      lsb_valid_o <= lsb_valid_i;  // One cycle later
      ldst_type   <= ldst_type_i;
    end
  end

  // ---------------------
  // VIRTUAL ADDRESS ADDER
  // ---------------------
  assign vaddr_o = rs1_value + imm_value;

  // -------------------------------
  // VIRTUAL ADDRESS EXCEPTION CHECK
  // -------------------------------
  always_comb begin : vaddr_exception
    // Check if the computed address is compliant to the SV39 or SV48 format. If not, an exception is registered. Upon commit, this will be interpreted as load/store PAGE FAULT EXCEPTION.
    case (vm_mode)
      SV39:    pfault_except = (vaddr_o[63:39] != {25{vaddr_o[38]}}) ? (1'b1) : (1'b0);
      SV48:    pfault_except = (vaddr_o[63:48] != {16{vaddr_o[47]}}) ? (1'b1) : (1'b0);
      default: pfault_except = 1'b0;
    endcase
    // Check if the address is naturally aligned according to the type of load/store. If not, an ADDRESS MISALIGNED exception must be raised.
    case (ldst_type)
      LS_HALFWORD, LS_HALFWORD_U: align_except = (vaddr_o[0]) ? (1'b1) : (1'b0);
      LS_WORD, LS_WORD_U:         align_except = (vaddr_o[1:0] != 2'b00) ? (1'b1) : (1'b0);
      LS_DOUBLEWORD:              align_except = (vaddr_o[2:0] != 3'b000) ? (1'b1) : (1'b0);
      default:                    align_except = 1'b0;
    endcase
    // Output the correct exception: address misaligned exceptions have higher priority than page fault exceptions
    except_o = VADDER_NO_EXCEPT;
    if (align_except) except_o = VADDER_ALIGN_EXCEPT;
    else if (pfault_except) except_o = VADDER_PAGE_EXCEPT;
    else except_o = VADDER_NO_EXCEPT;
  end

  // -------------
  // OTHER OUTPUTS
  // -------------
  assign lsb_ready_o = lsb_ready_i;  // ready when the LSB is

  // ----------
  // ASSERTIONS
  // ----------
`ifndef SYNTHESIS
  satp_mode_t vm_mode_e;
  always @(negedge clk_i) begin
    $cast(vm_mode_e, vm_mode);
    // Warn when an address exception is raised
    case (vm_mode)
      SV39:
      assert (vaddr_o[63:39] == {25{vaddr_o[38]}})
      else `$error($sformatf("MSBs [63:39] of virtual address are different from bit 38 while paging mode is %s", vm_mode_e.name()))
      SV48:
      assert (vaddr_o[63:48] == {16{vaddr_o[47]}})
      else `$error($sformatf("MSBs [63:48] of virtual address are different from bit 47 while paging mode is %s", vm_mode_e.name()))
      default: ;
    endcase
    // Warn when virtual address is misaligned
    case (ldst_type)
      LS_HALFWORD, LS_HALFWORD_U:
      assert (!vaddr_o[0])
      else `$error($sformatf("Instruction of type HALFWORD has misaligned address \'%h\'", vaddr_o))
      LS_WORD, LS_WORD_U:
      assert (vaddr_o[1:0] == 2'b00)
      else `$error($sformatf("Instruction of type WORD has misaligned address \'%h\'", vaddr_o))
      LS_DOUBLEWORD:
      assert (vaddr_o[2:0] == 3'b000)
      else `$error($sformatf("Instruction of type DOUBLEWORD has misaligned address \'%h\'", vaddr_o))
      default: ;
    endcase
  end
`endif

endmodule
