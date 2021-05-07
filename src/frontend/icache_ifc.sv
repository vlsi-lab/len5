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
// File: icache_ifc.sv
// Author: Marco Andorno
// Date: 02/10/2019

import len5_pkg::*;

module icache_ifc
(
  input   logic             clk_i,
  input   logic             rst_n_i,
  input   logic             flush_i,

  // From/to IF
  input   logic [XLEN-1:0]  pc_i, 
  input   logic             read_req_i,
  output  icache_out_t      cache_out_o,
  output  logic             read_done_o,

  // From/to icache
  output  logic [XLEN-1:0]  addr_o,
  output  logic             addr_valid_o,
  input   logic             addr_ready_i,
  input   var icache_out_t      data_i,
  input   logic             data_valid_i,
  output  logic             data_ready_o
);

  // =========== Datapath ============
  logic [XLEN-1:0] saved_pc;
  logic addr_sel;

  always_ff @(posedge clk_i or negedge rst_n_i) begin: addr_reg
    if (!rst_n_i) begin: async_rst
      saved_pc <= '0;
    end else begin
      if (read_req_i) begin
        saved_pc <= pc_i;
      end
    end
  end: addr_reg

  // Data assignment
  assign addr_o = addr_sel ? saved_pc : pc_i;
  assign cache_out_o = data_i;
  
  // ========= Control unit ===========
  // State definition
  typedef enum logic [1:0] { RESET, WAIT_REQ, ADDR_BUSY, WAIT_DATA } state_t;
  state_t present_state, next_state;

  // State transition
  always_ff @ (posedge clk_i or negedge rst_n_i) begin
    // Async reset
    if (~rst_n_i) begin
      present_state <= RESET;
    end else begin
      if (flush_i) begin
        present_state <= WAIT_REQ;
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
        next_state = WAIT_REQ;
      end

      WAIT_REQ: begin
        if (read_req_i) begin
          if (addr_ready_i) begin
            next_state = WAIT_DATA;
          end else begin
            next_state = ADDR_BUSY;
          end
        end else begin // idle loop until req arrives
          next_state = WAIT_REQ;
        end
      end

      // This state removes the need for read_req_i to 
      // remain active until the handshake occurs.
      ADDR_BUSY: begin
        if (addr_ready_i) begin
          next_state = WAIT_DATA;
        end else begin
          next_state = ADDR_BUSY;
        end
      end

      WAIT_DATA: begin
        if (data_valid_i) begin
          if (~read_req_i) begin
            next_state = WAIT_REQ;
          end else begin
            if (addr_ready_i) begin
              next_state = WAIT_DATA;
            end else begin
              next_state = ADDR_BUSY;
            end
          end
        end else begin
          next_state = WAIT_DATA;
        end
      end
    endcase
  end

  // Output update
  always_comb begin
    // Defaults
    addr_valid_o = 'b0;
    data_ready_o = 'b0;
    read_done_o = 'b0;
    addr_sel = 'b0;

    case (present_state)
      WAIT_REQ: begin
        if (read_req_i) begin
          addr_valid_o = 'b1;
        end
        // Moore output
        addr_sel = 'b0;
      end

      // This state removes the need for read_req_i to 
      // remain active until the handshake occurs.
      ADDR_BUSY: begin
        // Moore output
        addr_valid_o = 'b1;
        addr_sel = 'b1;
      end

      WAIT_DATA: begin
        if (data_valid_i) begin
          if (~read_req_i) begin
            read_done_o = 'b1;
          end else begin
            read_done_o = 'b1;
            addr_valid_o = 'b1;
          end
        end
        // Moore output
        data_ready_o = 'b1;
      end
    endcase
  end
  /* verilator lint_on CASEINCOMPLETE */
endmodule
