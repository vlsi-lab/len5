// Copyright 2021 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: alu.sv
// Author: Michele Caon
// Date: 10/11/2021

import len5_pkg::*;
import expipe_pkg::*;

module alu #(
  parameter int unsigned SKIP_REG = 0,  // make the ALU fully combinational

  // EU-specific parameters
  parameter int unsigned EU_CTL_LEN = 4
) (
  input logic clk_i,
  input logic rst_n_i,
  input logic flush_i,

  // Handshake from/to the reservation station unit
  input  logic valid_i,
  input  logic ready_i,
  output logic valid_o,
  output logic ready_o,

  // Data from/to the reservation station unit
  input  logic         [EU_CTL_LEN-1:0] ctl_i,
  input  rob_idx_t                      rob_idx_i,
  input  logic         [      XLEN-1:0] rs1_i,
  input  logic         [      XLEN-1:0] rs2_i,
  output rob_idx_t                      rob_idx_o,
  output logic         [      XLEN-1:0] result_o,
  output logic                          except_raised_o,
  output except_code_t                  except_code_o
);

  // ALU output
  logic [XLEN-1:0] result;
  logic            except_raised;

  // --------------
  // ALU OPERATIONS
  // --------------

  always_comb begin : alu_ops
    // Default values
    result        = '0;
    except_raised = 1'b0;

    unique case (ctl_i)
      ALU_ADD:  result = rs1_i + rs2_i;
      ALU_ADDW: result = signed'(rs1_i[(XLEN>>1)-1:0] + rs2_i[(XLEN>>1)-1:0]);
      ALU_SUB:  result = rs1_i - rs2_i;
      ALU_SUBW: result = signed'(rs1_i[(XLEN>>1)-1:0] - rs2_i[(XLEN>>1)-1:0]);
      ALU_AND:  result = rs1_i & rs2_i;
      ALU_OR:   result = rs1_i | rs2_i;
      ALU_XOR:  result = rs1_i ^ rs2_i;
      ALU_SLL:  result = rs1_i << rs2_i[5:0];
      ALU_SLLW: result = signed'(rs1_i[(XLEN>>1)-1:0] << rs2_i[4:0]);
      ALU_SRL:  result = rs1_i >> rs2_i[5:0];
      ALU_SRLW: result = {32'h0, rs1_i[(XLEN>>1)-1:0] >> rs2_i[4:0]};
      ALU_SRA:  result = rs1_i >>> rs2_i[5:0];
      ALU_SRAW: result = rs1_i[(XLEN>>1)-1:0] >>> rs2_i[4:0];
      ALU_SLT:  result = signed'(rs1_i) < signed'(rs2_i);
      ALU_SLTU: result = rs1_i < rs2_i;
      default:  except_raised = 1'b1;
    endcase
  end

  // Exception handling
  assign except_code = E_ILLEGAL_INSTRUCTION;  // invalid ALU opcode

  // ---------------
  // OUTPUT REGISTER
  // ---------------
  // NOTE: use a spill cell to break the handshaking path

  // Interface data type
  typedef struct packed {
    logic [XLEN-1:0] res;            // the ALU result
    rob_idx_t        rob_idx;        // instr. ROB index
    logic            except_raised;  // exception flag
  } out_reg_data_t;

  out_reg_data_t out_reg_data_in, out_reg_data_out;

  // Input data
  assign out_reg_data_in.res           = result;
  assign out_reg_data_in.rob_idx       = rob_idx_i;
  assign out_reg_data_in.except_raised = except_raised;

  // Output data
  assign result_o                      = out_reg_data_out.res;
  assign rob_idx_o                     = out_reg_data_out.rob_idx;
  assign except_raised_o               = out_reg_data_out.except_raised;

  // Output register
  spill_cell_flush #(
    .DATA_T(out_reg_data_t),
    .SKIP  (SKIP_REG)
  ) u_out_reg (
    .clk_i  (clk_i),
    .rst_n_i(rst_n_i),
    .flush_i(flush_i),
    .valid_i(valid_i),
    .ready_i(ready_i),
    .valid_o(valid_o),
    .ready_o(ready_o),
    .data_i (out_reg_data_in),
    .data_o (out_reg_data_out)
  );

  // Exception handling
  // ------------------
  assign except_code_o = E_ILLEGAL_INSTRUCTION;

endmodule
