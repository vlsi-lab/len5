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
// File: op_only_unit.sv
// Author: Michele Caon
// Date: 17/11/2021

/*
 * NOTE: For now it only handles CSR instructions, so the rs1_value
 * is provided as result to the reaorder buffer.
 */

import len5_config_pkg::*;
import len5_pkg::XLEN;
import expipe_pkg::ROB_IDX_LEN;
import expipe_pkg::cdb_data_t;
import expipe_pkg::rob_idx_t;

module op_only_unit #(
  RS_DEPTH = 4,  // must be a power of 2

  // EU-specific parameters
  EU_CTL_LEN = 4
) (
  // Clock, reset, and flush
  input logic clk_i,
  input logic rst_n_i,
  input logic flush_i,

  // Handshake from/to issue arbiter
  input  logic issue_valid_i,
  output logic issue_ready_o,

  // Data from the decode stage
  input logic                rs1_ready_i,
  input rob_idx_t            rs1_idx_i,
  input logic     [XLEN-1:0] rs1_value_i,
  input rob_idx_t            dest_idx_i,

  // Hanshake from/to the CDB
  input  logic cdb_ready_i,
  input  logic cdb_valid_i,  // to know if the CDB is carrying valid data
  output logic cdb_valid_o,

  // Data from/to the CDB
  input  cdb_data_t cdb_data_i,
  output cdb_data_t cdb_data_o
);

  // Instantiate reservation station
  // -------------------------------
  op_only_rs #(
    .RS_DEPTH  (RS_DEPTH),
    .EU_CTL_LEN(EU_CTL_LEN)
  ) u_op_only_rs (
    .clk_i        (clk_i),
    .rst_n_i      (rst_n_i),
    .flush_i      (flush_i),
    .issue_valid_i(issue_valid_i),
    .issue_ready_o(issue_ready_o),
    .rs1_ready_i  (rs1_ready_i),
    .rs1_idx_i    (rs1_idx_i),
    .rs1_value_i  (rs1_value_i),
    .dest_idx_i   (dest_idx_i),
    .cdb_ready_i  (cdb_ready_i),
    .cdb_valid_i  (cdb_valid_i),
    .cdb_valid_o  (cdb_valid_o),
    .cdb_data_i   (cdb_data_i),
    .cdb_data_o   (cdb_data_o)
  );

endmodule
