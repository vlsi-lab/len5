// Copyright 2024 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//

/* verilator lint_off UNUSED */

module jump_early_dec (
  input  len5_pkg::instr_t       instr_i,
  input  fetch_pkg::prediction_t mem_if_pred_i,
  input logic                   [len5_pkg::XLEN-1:0] early_jump_target_prediction_i,
  output fetch_pkg::prediction_t issue_pred_o,
  output logic                   early_jump_valid_o,
  output logic                   mem_flush_o,
  output logic                   [len5_pkg::XLEN-1:0] early_jump_target_o
);

  import len5_pkg::*;
  import instr_pkg::JAL;

  // INTERNAL SIGNALS
  // ----------------
  logic is_jump; // For resource sharing, in case synopsys fails recognizing it

  assign is_jump = ( instr_i.j.opcode == JAL[OPCODE_LEN-1:0] );
  // OUTPUTS
  assign early_jump_valid_o = is_jump;
  assign mem_flush_o = is_jump;
  // Get the offset to be added to the PC on 32 bits using sign extension
  assign early_jump_target_o = {{(XLEN-U_IMM-1){instr_i.j.imm20[0]}}, instr_i.j.imm20, instr_i.j.imm19, instr_i.j.imm11, instr_i.j.imm10, 1'b0};

  assign issue_pred_o.pc = mem_if_pred_i.pc;
  assign issue_pred_o.target = (is_jump) ? early_jump_target_prediction_i : mem_if_pred_i.target;
  assign issue_pred_o.taken = (is_jump) ? 1'b1 : mem_if_pred_i.taken;

endmodule
