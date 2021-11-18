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
// File: branch_ctl_cu.sv
// Author: Marco Andorno
// Date: 09/10/2019

import len5_pkg::*;

module branch_ctl_cu
(
  input   logic clk_i,
  input   logic rst_n_i,
  input   logic ops_valid_i,
  input   logic taken_i,
  input   logic wrong_taken_i,
  input   logic wrong_target_i,

  output  logic ops_ready_o,
  output  logic res_valid_o,
  output  logic res_taken_o,
  output  logic res_mispredict_o
);

  typedef enum logic [2:0] { RESET, WAIT_OPS, GOOD_T, GOOD_NT, BAD_T, BAD_NT } state_t;
  state_t present_state, next_state;

  // State transition
  always_ff @ (posedge clk_i or negedge rst_n_i) begin
    // Async reset
    if (!rst_n_i) begin
      present_state <= RESET;
    end else begin
      present_state <= next_state;
    end
  end

  // State update
  always_comb begin
    // Defaults
    next_state = RESET;

    case (present_state)
      RESET: begin
        next_state = WAIT_OPS;
      end

      WAIT_OPS: begin
        if (ops_valid_i) begin
          if (taken_i) begin
            if (wrong_taken_i || wrong_target_i) begin
              next_state = BAD_T;
            end else begin
              next_state = GOOD_T;
            end
          end else begin
            if (wrong_taken_i) begin
              next_state = BAD_NT;
            end else begin
              next_state = GOOD_NT;
            end
          end
        end else begin
          next_state = WAIT_OPS;
        end
      end

      GOOD_T: begin
        next_state = WAIT_OPS;
      end

      GOOD_NT: begin
        next_state = WAIT_OPS;
      end

      BAD_T: begin
        next_state = WAIT_OPS;
      end

      BAD_NT: begin
        next_state = WAIT_OPS;
      end

      default: begin
        next_state = RESET;
      end
    endcase
  end

  // Output update
  always_comb begin
    // Defaults
    ops_ready_o = '0;
    res_valid_o = '0;
    res_taken_o = '0;
    res_mispredict_o = '0;

    case (present_state)
      WAIT_OPS: begin
        ops_ready_o = '1;
      end

      GOOD_T: begin
        res_taken_o = '1;
        res_mispredict_o = '0;
        res_valid_o = '1;
      end

      GOOD_NT: begin
        res_taken_o = '0;
        res_mispredict_o = '0;
        res_valid_o = '1;
      end

      BAD_T: begin
        res_taken_o = '1;
        res_mispredict_o = '1;
        res_valid_o = '1;
      end

      BAD_NT: begin
        res_taken_o = '0;
        res_mispredict_o = '1;
        res_valid_o = '1;
      end

      default:;
    endcase
  end
  
endmodule
