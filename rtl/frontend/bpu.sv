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
// File: bpu.sv
// Author: Marco Andorno
// Date: 7/8/2019

module bpu #(
  parameter int unsigned     HLEN     = 4,
  parameter int unsigned     BTB_BITS = 4,
  parameter fetch_pkg::c2b_t INIT_C2B = fetch_pkg::WNT
) (
  input logic                                        clk_i,
  input logic                                        rst_ni,
  input logic                                        flush_i,
  input logic                   [len5_pkg::XLEN-1:0] curr_pc_i,
  input logic                                        bu_res_valid_i,
  input fetch_pkg::resolution_t                      bu_res_i,

  output fetch_pkg::prediction_t pred_o
);

  import len5_pkg::*;
  import fetch_pkg::*;
  // Signal definitions
  logic btb_hit, btb_update, btb_del_entry;
  logic                   gshare_taken;
  logic [XLEN-OFFSET-1:0] btb_target;

  // Module instantiations
  gshare #(
    .HLEN    (HLEN),
    .INIT_C2B(INIT_C2B)
  ) u_gshare (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .flush_i    (flush_i),
    .curr_pc_i  (curr_pc_i),
    .res_valid_i(bu_res_valid_i),
    .res_taken_i(bu_res_i.taken),
    .res_hist_i (bu_res_i.pc[HLEN+OFFSET-1:OFFSET]),
    .taken_o    (gshare_taken)
  );

  btb #(
    .BTB_BITS(BTB_BITS)
  ) u_btb (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),
    .flush_i     (flush_i),
    .curr_pc_i   (curr_pc_i),
    .valid_i     (btb_update),
    .del_entry_i (btb_del_entry),
    .res_pc_i    (bu_res_i.pc),
    .res_target_i(bu_res_i.target),
    .hit_o       (btb_hit),
    .target_o    (btb_target)
  );

  // Assignments
  assign btb_update    = bu_res_valid_i;
  assign btb_del_entry = bu_res_i.mispredict & ~bu_res_i.taken;  // Why delete?
  assign pred_o.pc     = curr_pc_i;
  assign pred_o.taken  = gshare_taken & btb_hit;
  assign pred_o.target = {btb_target, 2'b00};
endmodule
