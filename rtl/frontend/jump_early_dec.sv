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
  input logic clk_i,
  input logic rst_ni,
  input logic flush_i,

  input  len5_pkg::instr_t                            instr_i,
  input  logic                                        instr_valid_i,
  input  logic                                        issue_ready_i,
  input  fetch_pkg::prediction_t                      mem_if_pred_i,
  input  logic                   [len5_pkg::XLEN-1:0] early_jump_target_i,
  input  logic                   [len5_pkg::XLEN-1:0] rf_ra_value_i,
  output fetch_pkg::prediction_t                      issue_pred_o,
  output logic                                        early_jump_valid_o,
  output logic                                        mem_flush_o,
  output logic                   [len5_pkg::XLEN-1:0] early_jump_offs_o,
  output logic                   [len5_pkg::XLEN-1:0] early_jump_base_o
);

  import len5_pkg::*;
  import instr_pkg::JAL;
  import instr_pkg::JALR;

  // PARAMETERS
  localparam logic [ILEN-1:0] RET = {12'b0, 5'b00001, 3'b000, 5'b00000, JALR[OPCODE_LEN-1:0]};

  // INTERNAL SIGNALS
  // ----------------
  // JUMP type
  typedef enum logic [1:0] {
    JUMP_TYPE_JAL,
    JUMP_TYPE_RET,
    JUMP_TYPE_NONE
  } jump_type_t;
  jump_type_t jump_type;

  // FSM state
  typedef enum logic [1:0] {
    RESET,
    IDLE,
    WAIT_ISSUE
  } fsm_state_t;
  fsm_state_t curr_state, next_state;
  logic is_jump;  // For resource sharing, in case synopsys fails recognizing it

  // Target address
  logic [ALEN-1:0] early_jump_base, early_jump_offs;

  // --------------------
  // FINITE STATE MACHINE
  // --------------------
  // Jump instruction decoder
  always_comb begin : jump_dec
    // TODO: replace with RAS once it is implemented
    if (instr_i.raw == RET) jump_type = JUMP_TYPE_RET;
    else if (instr_i.j.opcode == JAL[OPCODE_LEN-1:0]) jump_type = JUMP_TYPE_JAL;
    else jump_type = JUMP_TYPE_NONE;
  end

  // jal instruction decoder
  assign is_jump = jump_type != JUMP_TYPE_NONE;

  // State transition logic
  always_comb begin : fsm_state_net
    unique case (curr_state)
      RESET:   next_state = IDLE;
      IDLE: begin
        if (instr_valid_i && is_jump) begin
          if (!issue_ready_i) next_state = WAIT_ISSUE;
          else next_state = IDLE;
        end else next_state = IDLE;
      end
      WAIT_ISSUE: begin
        if (issue_ready_i) next_state = IDLE;
        else next_state = WAIT_ISSUE;
      end
      default: next_state = IDLE;
    endcase
  end

  // Output network
  always_comb begin : fsm_out_net
    // Default values
    early_jump_valid_o = 1'b0;
    mem_flush_o        = 1'b0;

    unique case (curr_state)
      IDLE: begin
        early_jump_valid_o = is_jump & instr_valid_i;
        mem_flush_o        = is_jump & instr_valid_i & issue_ready_i;
      end
      WAIT_ISSUE: begin
        early_jump_valid_o = 1'b1;
        mem_flush_o        = issue_ready_i;
      end
      default: ;  // use default values
    endcase
  end

  // State register
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) curr_state <= RESET;
    else if (flush_i) curr_state <= IDLE;
    else curr_state <= next_state;
  end

  // Output network
  // --------------
  // Target address multiplexer
  always_comb begin : target_addr_mux
    unique case (jump_type)
      JUMP_TYPE_RET: begin
        early_jump_base = '0;
        early_jump_offs = rf_ra_value_i;
      end
      default: begin
        early_jump_base = mem_if_pred_i.pc;
        early_jump_offs = XLEN'(signed'({
          instr_i.j.imm20, instr_i.j.imm19, instr_i.j.imm11, instr_i.j.imm10, 1'b0
        }));
      end
    endcase
  end

  // Target address for the PC generation unit
  assign early_jump_base_o   = early_jump_base;
  assign early_jump_offs_o   = early_jump_offs;

  // Prediction for the execution stage
  assign issue_pred_o.pc     = mem_if_pred_i.pc;
  assign issue_pred_o.target = (is_jump) ? early_jump_target_i : mem_if_pred_i.target;
  assign issue_pred_o.taken  = is_jump | mem_if_pred_i.taken;
endmodule
