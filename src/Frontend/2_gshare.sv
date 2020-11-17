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
// File: gshare.sv
// Author: Marco Andorno
// Date: 26/07/2019

`include "/home/phd-students/walid.walid/Desktop/RISC/len5_core_master/include/len5_pkg.sv"
import len5_pkg::*;

/* verilator lint_off BLKLOOPINIT */
module gshare
#(
  parameter HLEN = 4
)
(
  input   logic             clk_i,
  input   logic             rst_n_i,
  input   logic             flush_i,
  input   logic [XLEN-1:0]  pc_i,
  input   resolution_t      res_i,

  output  logic             taken_o
);

  // Definitions
  typedef enum logic [1:0] {SNT, WNT, WT, ST} c2b_t; // 2-bit counter enum
  localparam c2b_t INIT_C2B = SNT;
  localparam PHT_ROWS = 1 << HLEN;
  c2b_t pht_d[PHT_ROWS], pht_q[PHT_ROWS];
  
  logic [HLEN-1:0] history, index_r, index_w;

  // --------------------------
  // Branch History Table (BHT)
  // --------------------------
  always_ff @(posedge clk_i or negedge rst_n_i) begin: bht
    if (!rst_n_i) begin: bht_async_rst
      history <= '0;
    end else begin
      if (flush_i) begin: bht_sync_flush
        history <= '0;
      end else if (res_i.valid) begin: bht_shift
        history <= {history[HLEN-2:0], res_i.taken};
      end
    end
  end: bht

  // ---------------------------
  // Pattern History Table (PHT)
  // ---------------------------
  always_comb begin: pht_update
    // By default, store previous values
    pht_d = pht_q;

    // If a valid branch resolution arrives, update counters
    if (res_i.valid) begin: c2b_fsm
      case (pht_q[index_w])
        SNT: begin
          if (res_i.taken)
            pht_d[index_w] = WNT;
          else pht_d[index_w] = SNT;
        end

        WNT: begin
          if (res_i.taken)
            pht_d[index_w] = WT;
          else pht_d[index_w] = SNT;
        end

        WT: begin
          if (res_i.taken)
            pht_d[index_w] = ST;
          else pht_d[index_w] = WNT;
        end

        ST: begin
          if (res_i.taken)
            pht_d[index_w] = ST;
          else pht_d[index_w] = WT;
        end

        default: pht_d[index_w] = WNT;
      endcase
    end: c2b_fsm
  end: pht_update

  always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin: pht_async_rst
      for (int i = 0; i < PHT_ROWS; i++) begin
        pht_q[i] <= INIT_C2B;
      end
    end
    else if (flush_i) begin: pht_sync_flush
      for (int i = 0; i < PHT_ROWS; i++) begin
        pht_q[i] <= INIT_C2B;
      end
    end
    else pht_q <= pht_d;
  end
    
  // Assignments
  assign index_r = history ^ pc_i[HLEN + OFFSET - 1:OFFSET]; // XOR hashing
  assign index_w = history ^ res_i.pc[HLEN + OFFSET - 1:OFFSET];
  assign taken_o = pht_q[index_r][1];

endmodule
/* verilator lint_on BLKLOOPINIT */
