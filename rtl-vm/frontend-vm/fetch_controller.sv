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
// File: fetch_controller.sv
// Author: Marco Andorno
// Date: 27/09/2019

import len5_pkg::*;

module fetch_controller (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic here_i,
    input logic will_be_here_i,
    input logic issue_ready_i,
    input logic read_done_i,

    output logic      fetch_ready_o,
    output logic      read_req_o,
    output logic      issue_valid_o,
    output pc_src_t   pc_sel_o,
    output line_src_t line_sel_o
);

  typedef enum logic [2:0] {
    RESET,
    STARTUP,
    CACHE_REQ,
    SEL_IN_LINE,
    SEL_IN_BACKUP
  } state_t;
  state_t present_state, next_state;

  // State transition
  always_ff @(posedge clk_i or negedge rst_n_i) begin
    // Async reset
    if (!rst_n_i) begin
      present_state <= RESET;
    end else begin
      if (flush_i) begin
        present_state <= STARTUP;
      end else begin
        present_state <= next_state;
      end
    end
  end

  /* verilator lint_off CASEINCOMPLETE */
  // State update
  always_comb begin
    // Defaults
    next_state = RESET;

    case (present_state)
      RESET: begin
        next_state = STARTUP;
      end

      STARTUP: begin
        next_state = CACHE_REQ;
      end

      CACHE_REQ: begin
        if (read_done_i) begin
          if (issue_ready_i) begin
            if (here_i) begin
              next_state = SEL_IN_BACKUP;
            end else if (will_be_here_i) begin
              next_state = SEL_IN_LINE;
            end else begin
              next_state = CACHE_REQ;
            end
          end else begin
            // This way, instructions can be lost and must
            // be re-fetched if they were in line backup
            next_state = SEL_IN_LINE;
          end
        end else begin  // loop until cache is done
          next_state = CACHE_REQ;
        end
      end

      SEL_IN_LINE: begin
        if (issue_ready_i) begin
          if (here_i) begin
            next_state = SEL_IN_LINE;
          end else begin
            next_state = CACHE_REQ;
          end
        end else begin  // loop until issue is ready
          next_state = SEL_IN_LINE;
        end
      end

      SEL_IN_BACKUP: begin
        if (issue_ready_i) begin
          if (here_i) begin
            next_state = SEL_IN_LINE;
          end else begin
            next_state = CACHE_REQ;
          end
        end else begin
          // Line bak register must be disabled
          next_state = SEL_IN_BACKUP;
        end
      end
    endcase
  end

  // Output update
  always_comb begin
    // Defaults
    fetch_ready_o = 'b0;
    read_req_o = 'b0;
    pc_sel_o = prev_pc;
    line_sel_o = line_reg;
    issue_valid_o = 'b0;

    case (present_state)
      STARTUP: begin
        // Moore outputs
        fetch_ready_o = 'b1;
        read_req_o = 'b1;
      end

      CACHE_REQ: begin
        if (read_done_i) begin
          if (issue_ready_i) begin
            if (here_i || will_be_here_i) begin
              fetch_ready_o = 'b1;
              pc_sel_o = prev_pc;
              line_sel_o = cache_out;
              issue_valid_o = 'b1;
            end else begin
              fetch_ready_o = 'b1;
              read_req_o = 'b1;
              pc_sel_o = prev_pc;
              line_sel_o = cache_out;
              issue_valid_o = 'b1;
            end
          end else begin
            // This way, instructions can be lost and must
            // be re-fetched if they were in line backup
            fetch_ready_o = 'b0;
          end
        end else begin
          fetch_ready_o = 'b0;
          issue_valid_o = 'b0;
        end
      end

      SEL_IN_LINE: begin
        if (issue_ready_i) begin
          if (here_i) begin
            fetch_ready_o = 'b1;
            line_sel_o = line_reg;
          end else begin
            fetch_ready_o = 'b1;
            read_req_o = 'b1;
            line_sel_o = line_reg;
          end
        end else begin
          fetch_ready_o = 'b0;
        end
        // Moore outputs
        issue_valid_o = 'b1;
      end

      SEL_IN_BACKUP: begin
        if (issue_ready_i) begin
          if (here_i) begin
            fetch_ready_o = 'b1;
            pc_sel_o = prev_pc;
            line_sel_o = line_bak;
          end else begin
            fetch_ready_o = 'b1;
            read_req_o = 'b1;
            pc_sel_o = prev_pc;
            line_sel_o = line_bak;
          end
        end else begin
          // Line bak register must be disabled
          fetch_ready_o = 'b0;
        end
        // Moore outputs
        issue_valid_o = 'b1;
      end
    endcase
  end
  /* verilator lint_on CASEINCOMPLETE */

endmodule
