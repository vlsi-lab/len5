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
// File: spill_cell_flush_cu.sv
// Author: Michele Caon
// Date: 10/11/2021

// -------------
// SPILL CELL CU
// -------------
// Controls a couple of registers based on handshaking signals. When the
// downstream hardware is not ready, buffer input data on a spill register
// and lower the output ready for the upstream hardware in the next cycle.

module spill_cell_flush_cu (
  // Clock, reset, and flush
  input logic clk_i,
  input logic rst_n_i,
  input logic flush_i,

  // Handshaking signals
  input  logic valid_i,  // from upstream hardware
  input  logic ready_i,  // from downstream hardware
  output logic valid_o,  // from downstream hardware
  output logic ready_o,  // from upstream hardware

  // Output control signals
  output logic a_en_o,  // enable for the first register
  output logic b_en_o,  // enable for the second (spill) register
  output logic b_sel_o  // for register MUX
);

  // ----------------
  // INTERNAL SIGNALS
  // ----------------

  // CU state
  typedef enum logic [2:0] {
    RESET,
    NO_DATA,
    A_FULL,
    B_FULL,
    AB_FULL_SEL_A,
    AB_FULL_SEL_B
  } cu_state_t;
  cu_state_t curr_state, next_state;

  // ------------
  // CONTROL UNIT
  // ------------

  // State progression
  always_comb begin : cu_state_prog
    case (curr_state)
      // Reset state
      RESET: next_state = NO_DATA;

      // A and B registers are empty
      // If there's new data available, store it in A
      NO_DATA: begin
        if (valid_i) next_state = A_FULL;
        else next_state = NO_DATA;
      end

      // A register is full
      // Store new data in B. If the downstream hardware can accept the
      // data in A, consume it (move to B_FULL).
      A_FULL: begin
        if (valid_i && ready_i) next_state = B_FULL;
        else if (valid_i && !ready_i) next_state = AB_FULL_SEL_A;
        else if (!valid_i && ready_i) next_state = NO_DATA;
        else next_state = A_FULL;
      end

      // B register is full
      // Store new data in A. If the downstream hardware can accept the
      // data in B, consume it (move to A_FULL).
      B_FULL: begin
        if (valid_i && ready_i) next_state = A_FULL;
        else if (valid_i && !ready_i) next_state = AB_FULL_SEL_B;
        else if (!valid_i && ready_i) next_state = NO_DATA;
        else next_state = B_FULL;
      end

      // Both A and B registers are full (active data in A)
      // Once the downstream hardware can accept the data in A, store
      // new incoming data in B and select it for the next cycle.
      AB_FULL_SEL_A: begin
        if (ready_i) next_state = B_FULL;
        else next_state = AB_FULL_SEL_A;
      end

      // Both A and B registers are full (active data in B)
      // Once the downstream hardware can accept the data in B, store
      // new incoming data in A and select it for the next cycle.
      AB_FULL_SEL_B: begin
        if (ready_i) next_state = A_FULL;
        else next_state = AB_FULL_SEL_B;
      end

      // Unknown state
      default: next_state = RESET;
    endcase
  end

  // Output evaluation
  // NOTE: Mealy machine that uses valid_i to enable the regs and save power
  always_comb begin : cu_out_eval
    // Default values
    ready_o = 1'b0;
    valid_o = 1'b0;
    a_en_o  = 1'b0;
    b_en_o  = 1'b0;
    b_sel_o = 1'b0;

    case (curr_state)
      RESET:   ;  // use default values
      NO_DATA: begin
        ready_o = !flush_i;  // new data can be accepted
        valid_o = 1'b0;  // no valid data in A or B
        a_en_o  = valid_i;  // save incoming data in A
        b_en_o  = 1'b0;  // use A instead
        b_sel_o = 1'b0;
      end
      A_FULL: begin
        ready_o = !flush_i;  // new data can be accepted
        valid_o = 1'b1;  // valid data in A
        a_en_o  = 1'b0;  // keep old data in A
        b_en_o  = valid_i;  // store new data in B
        b_sel_o = 1'b0;  // select data in A
      end
      B_FULL: begin
        ready_o = !flush_i;  // new data can be accepted
        valid_o = 1'b1;  // valid data in B
        a_en_o  = valid_i;  // store new data in A
        b_en_o  = 1'b0;  // keep old data in B
        b_sel_o = 1'b1;  // select data in B
      end
      AB_FULL_SEL_A: begin
        ready_o = 1'b0;  // do not accept new data
        valid_o = 1'b1;  // valid data in A
        a_en_o  = 1'b0;  // no data to store
        b_en_o  = 1'b0;  // no data to store
        b_sel_o = 1'b0;  // select data in A
      end
      AB_FULL_SEL_B: begin
        ready_o = 1'b0;  // do not accept new data
        valid_o = 1'b1;  // valid data in B
        a_en_o  = 1'b0;  // no data to store
        b_en_o  = 1'b0;  // no data to store
        b_sel_o = 1'b1;  // select data in B
      end
      default: ;  // use default values
    endcase
  end

  // State update
  always_ff @(posedge clk_i or negedge rst_n_i) begin : cu_state_upd
    if (!rst_n_i) curr_state <= RESET;  // asynchronous reset
    else if (flush_i) curr_state <= NO_DATA;  // synchronous flush
    else curr_state <= next_state;  // normal behaviour
  end

endmodule
