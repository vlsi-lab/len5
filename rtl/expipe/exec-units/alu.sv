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

module alu #(
  parameter bit SKIP_REG = 1'b0,  // make the ALU fully combinational

  // EU-specific parameters
  parameter int unsigned EU_CTL_LEN = 4
) (
  input logic clk_i,
  input logic rst_ni,
  input logic flush_i,

  // Handshake from/to the reservation station unit
  input  logic valid_i,
  input  logic ready_i,
  output logic valid_o,
  output logic ready_o,

  // Data from/to the reservation station unit
  input  logic                 [    EU_CTL_LEN-1:0] ctl_i,
  input  expipe_pkg::rob_idx_t                      rob_idx_i,
  input  logic                 [len5_pkg::XLEN-1:0] rs1_i,
  input  logic                 [len5_pkg::XLEN-1:0] rs2_i,
  output expipe_pkg::rob_idx_t                      rob_idx_o,
  output logic                 [len5_pkg::XLEN-1:0] result_o
);

  import len5_pkg::*;
  import expipe_pkg::*;

  // INTERNAL SIGNALS
  // ----------------
  // 32-bit operands
  logic [        XLEN-1:0] rs1_32_sext;
  logic [        XLEN-1:0] rs2_32_sext;

  // Adder
  logic [        XLEN-1:0] adder_a;
  logic [        XLEN-1:0] adder_b;
  logic                    adder_cin;  // carry-in
  logic [        XLEN-1:0] adder_res;
  logic [        XLEN-1:0] adder_res_32;

  // Shifter
  logic [        XLEN-1:0] shifter_rs1_rev;
  logic [          XLEN:0] shifter_a;
  logic [$clog2(XLEN)-1:0] shifter_shamt;
  logic [          XLEN:0] shifter_res;
  logic [        XLEN-1:0] shifter_res_rev;

  // ALU output
  logic [        XLEN-1:0] result;

  // --------------
  // ALU OPERATIONS
  // --------------
  // Sign-extenders for 32-bit operations
  assign rs1_32_sext = {{32{rs1_i[(XLEN>>1)-1]}}, rs1_i[(XLEN>>1)-1:0]};
  assign rs2_32_sext = {{32{rs2_i[(XLEN>>1)-1]}}, rs2_i[(XLEN>>1)-1:0]};

  // Adder
  // -----
  // Adder operands multiplexer
  always_comb begin : adder_op_mux
    unique case (ctl_i)
      ALU_SUB: begin
        adder_a   = rs1_i;
        adder_b   = ~rs2_i;
        adder_cin = 1'b1;
      end
      ALU_ADDW: begin
        adder_a   = rs1_32_sext;
        adder_b   = rs2_32_sext;
        adder_cin = 1'b0;
      end
      ALU_SUBW: begin
        adder_a   = rs1_32_sext;
        adder_b   = ~rs2_32_sext;
        adder_cin = 1'b1;
      end
      default: begin  // ALU_ADD
        adder_a   = rs1_i;
        adder_b   = rs2_i;
        adder_cin = 1'b0;
      end
    endcase
  end

  // 64-bit adder
  assign adder_res    = adder_a + adder_b + {{XLEN - 1{1'b0}}, adder_cin};

  // Result sign-extender for 32-bit operations
  assign adder_res_32 = {{32{adder_res[(XLEN>>1)-1]}}, adder_res[(XLEN>>1)-1:0]};

  // Shifter
  // -------
  // Shift operand multiplexer
  always_comb begin : shifter_a_mux
    unique case (ctl_i)
      ALU_SRL:  shifter_a = {1'b0, rs1_i};
      ALU_SRA:  shifter_a = {rs1_i[XLEN-1], rs1_i};
      ALU_SLLW: shifter_a = {{33{1'b0}}, shifter_rs1_rev[XLEN-1:XLEN>>1]};
      ALU_SRLW: shifter_a = {{33{1'b0}}, rs1_i[(XLEN>>1)-1:0]};
      ALU_SRAW: shifter_a = {{33{rs1_i[(XLEN>>1)-1]}}, rs1_i[(XLEN>>1)-1:0]};
      default:  shifter_a = {1'b0, shifter_rs1_rev};  // ALU_SLL
    endcase
  end

  // Shift amount multiplexer
  always_comb begin : shamt_mux
    unique case (ctl_i)
      ALU_SLLW, ALU_SRLW, ALU_SRAW: begin
        shifter_shamt = {1'b0, rs2_i[$clog2(XLEN>>1)-1:0]};
      end
      default: begin  // ALU_SLL, ALU_SRL, ALU_SRA
        shifter_shamt = rs2_i[$clog2(XLEN)-1:0];
      end
    endcase
  end

  // 65-bit arithmetic right barrel shifter
  assign shifter_res = shifter_a >>> shifter_shamt;

  // Left shift reverse operand and result
  generate
    for (genvar i = 0; i < XLEN; i++) begin : gen_shift_res_rev
      assign shifter_res_rev[i] = shifter_res[XLEN-i-1];
    end
  endgenerate
  generate
    for (genvar i = 0; i < XLEN; i++) begin : gen_shift_a_rev
      assign shifter_rs1_rev[i] = rs1_i[XLEN-i-1];
    end
  endgenerate

  // Result multiplexer
  // ------------------
  always_comb begin : result_mux
    // Default values
    result = '0;

    unique case (ctl_i)
      ALU_ADDW, ALU_SUBW:                   result = adder_res_32;  // TODO: check
      ALU_AND:                              result = rs1_i & rs2_i;
      ALU_OR:                               result = rs1_i | rs2_i;
      ALU_XOR:                              result = rs1_i ^ rs2_i;
      ALU_SLL, ALU_SLLW:                    result = shifter_res_rev;  // TODO: check
      ALU_SRL, ALU_SRA, ALU_SRLW, ALU_SRAW: result = shifter_res[XLEN-1:0];  // TODO: check
      ALU_SLT:                              result = {{XLEN-1{1'b0}}, ($signed(rs1_i) < $signed(rs2_i))};  // TODO: implement with adder res
      ALU_SLTU:                             result = {{XLEN-1{1'b0}}, (rs1_i < rs2_i)};  // TODO: implement with adder res
      default:                              result = adder_res;  // ALU_ADD, ALU_SUB
    endcase
  end

  // ---------------
  // OUTPUT REGISTER
  // ---------------
  // NOTE: use a spill cell to break the handshaking path

  // Interface data type
  typedef struct packed {
    logic [XLEN-1:0] res;      // the ALU result
    rob_idx_t        rob_idx;  // instr. ROB index
  } out_reg_data_t;

  out_reg_data_t out_reg_data_in, out_reg_data_out;

  // Input data
  assign out_reg_data_in.res     = result;
  assign out_reg_data_in.rob_idx = rob_idx_i;

  // Output data
  assign result_o                = out_reg_data_out.res;
  assign rob_idx_o               = out_reg_data_out.rob_idx;

  // Output register
  spill_cell_flush #(
    .DATA_T(out_reg_data_t),
    .SKIP  (SKIP_REG)
  ) u_out_reg (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .flush_i(flush_i),
    .valid_i(valid_i),
    .ready_i(ready_i),
    .valid_o(valid_o),
    .ready_o(ready_o),
    .data_i (out_reg_data_in),
    .data_o (out_reg_data_out)
  );
endmodule
