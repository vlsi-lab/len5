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
// File: int_rf.sv
// Author: Michele Caon
// Date: 12/11/2019

module int_rf (
  input logic clk_i,
  input logic rst_ni,

  // Handshake from the commit logic
  input logic comm_valid_i,
  // output  logic                   comm_ready_o,

  // Data from the commit logic (result write port)
  input logic [len5_pkg::REG_IDX_LEN-1:0] comm_rd_idx_i,
  input logic [       len5_pkg::XLEN-1:0] comm_rd_value_i,

  // Data to the issue stage (operands read ports)
  input  logic [len5_pkg::REG_IDX_LEN-1:0] issue_rs1_idx_i,
  input  logic [len5_pkg::REG_IDX_LEN-1:0] issue_rs2_idx_i,
  output logic [       len5_pkg::XLEN-1:0] issue_rs1_value_o,
  output logic [       len5_pkg::XLEN-1:0] issue_rs2_value_o,

  // Data to the fetch stage
  output logic [len5_pkg::XLEN-1:0] fetch_ra_value_o
);

  import len5_pkg::XLEN;
  import len5_pkg::XREG_NUM;
  import expipe_pkg::*;

  // DEFINITIONS

  // Register file data
  logic [XLEN-1:0] rf_data[1:XREG_NUM-1];

  // ------------------------
  // REGISTER FILE WRITE PORT
  // ------------------------
  // Synchronous write
  always_ff @(posedge clk_i or negedge rst_ni) begin : res_write_port
    if (!rst_ni) begin  // Asynchronous reset
      for (int i = 1; i < XREG_NUM; i++) begin
        rf_data[i] <= 0;
      end
    end else begin
      if (comm_valid_i && |comm_rd_idx_i) begin  // if the data from the commit stage is valid, update the RF
        rf_data[comm_rd_idx_i] <= comm_rd_value_i;
      end
    end
  end

  // ------------------------
  // REGISTER FILE READ PORTS
  // ------------------------
  // Asynchronous read
  always_comb begin : operands_read_ports
    // READ PORT 1 (rs1)
    if (|issue_rs1_idx_i) issue_rs1_value_o = rf_data[issue_rs1_idx_i];
    else issue_rs1_value_o = '0;
    // READ PORT 2 (rs2)
    if (|issue_rs2_idx_i) issue_rs2_value_o = rf_data[issue_rs2_idx_i];
    else issue_rs2_value_o = '0;
  end

  // Return address register (ra) for the fetch stage
  assign fetch_ra_value_o = rf_data[1];
endmodule
