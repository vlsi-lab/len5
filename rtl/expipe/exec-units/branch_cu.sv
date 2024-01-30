// Copyright 2022 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: branch_cu.sv
// Author: Michele Caon
// Date: 11/10/2022

/**
 * @brief Branch unit control unit
 *
 * @details This module implements a simple control unit that handles the
 *          notification of a misprediction to the frontend.
 */

module branch_cu (
  input  logic clk_i,
  input  logic rst_n_i,
  input  logic flush_i,
  input  logic valid_i,
  input  logic misprediction_i,
  input  logic fe_ready_i,
  output logic issue_mis_o,      // notify issue about the mispred.
  output logic fe_res_valid_o,   // send the resolution to the FE
  output logic bu_mis_reg_en_o
);
  // INTERNAL SIGNALS
  // ----------------
  // CU state
  typedef enum logic [2:0] {
    IDLE,
    UPD_FE,
    MIS,
    MIS_LOAD_PC,
    STALL
  } cu_state_t;
  cu_state_t curr_state, next_state;

  // ------------
  // CONTROL UNIT
  // ------------

  // State progression
  always_comb begin : cu_state_prog
    case (curr_state)
      IDLE: begin  // wait for a misprediction to occur
        if (valid_i && misprediction_i) next_state = MIS;
        else if (valid_i && !misprediction_i) next_state = UPD_FE;
        else next_state = IDLE;
      end
      UPD_FE: begin
        if (valid_i && misprediction_i) next_state = MIS;
        else if (valid_i && !misprediction_i) next_state = UPD_FE;
        else next_state = IDLE;
      end
      MIS:     next_state = MIS_LOAD_PC;
      MIS_LOAD_PC: begin
        if (fe_ready_i) next_state = STALL;
        else next_state = MIS_LOAD_PC;
      end
      STALL:   next_state = STALL;  // until flush
      default: next_state = IDLE;
    endcase
  end

  // Output evaluation
  always_comb begin : cu_out_eval
    // Default values
    issue_mis_o     = 1'b0;
    fe_res_valid_o  = 1'b0;
    bu_mis_reg_en_o = 1'b0;
    case (curr_state)
      IDLE: begin
        bu_mis_reg_en_o = 1'b1;
      end
      UPD_FE: begin
        bu_mis_reg_en_o = 1'b1;
        fe_res_valid_o  = 1'b1;
      end
      MIS: begin
        issue_mis_o = 1'b1;
      end
      MIS_LOAD_PC: begin
        fe_res_valid_o = 1'b1;
      end
      STALL:   ;  // use default values
      default: ;  // use default values
    endcase
  end

  // State update
  always_ff @(posedge clk_i or negedge rst_n_i) begin : cu_state_upd
    if (!rst_n_i) curr_state <= IDLE;
    else if (flush_i) curr_state <= IDLE;
    else curr_state <= next_state;
  end

  // ----------
  // DEBUG CODE
  // ----------
`ifndef SYNTHESIS
  property p_fe_valid;
    @(posedge clk_i) disable iff (!rst_n_i)
        sync_accept_on(flush_i)
        (curr_state == IDLE || curr_state == UPD_FE) && valid_i && misprediction_i |-> ##1
            fe_res_valid_o |-> ##[0:10]
            fe_ready_i |-> ##1
            !fe_res_valid_o
  endproperty
  a_fe_valid :
  assert property (p_fe_valid);
  property p_wait_flush;
    @(posedge clk_i) disable iff (!rst_n_i) curr_state == STALL & !flush_i |-> ##[1:2] !fe_res_valid_o
  endproperty
  a_wait_flush :
  assert property (p_wait_flush);
`endif  /* SYNTHESIS */
endmodule
