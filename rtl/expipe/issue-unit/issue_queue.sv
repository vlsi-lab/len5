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
// File: issue_queue.sv
// Author: Michele Caon
// Date: 17/10/2019

module issue_queue (
  input logic clk_i,
  input logic rst_ni,
  input logic flush_i,

  // Handshake from/to fetch unit
  input  logic fetch_valid_i,
  output logic fetch_ready_o,

  // Data from fetch unit
  input logic                   [len5_pkg::XLEN-1:0] curr_pc_i,
  input logic                   [len5_pkg::ILEN-1:0] instruction_i,
  input logic                   [len5_pkg::XLEN-1:0] pred_target_i,
  input logic                                        pred_taken_i,
  input logic                                        except_raised_i,
  input len5_pkg::except_code_t                      except_code_i,

  // Handshake from/to the issue logic
  input  logic issue_ready_i,
  output logic issue_valid_o,

  // Data to the execution pipeline
  output logic                   [len5_pkg::XLEN-1:0] curr_pc_o,
  output logic                   [len5_pkg::ILEN-1:0] instruction_o,
  output logic                   [len5_pkg::XLEN-1:0] pred_target_o,
  output logic                                        pred_taken_o,
  output logic                                        except_raised_o,
  output len5_pkg::except_code_t                      except_code_o
);
  import len5_pkg::*;
  import expipe_pkg::*;

  // DEFINITIONS
  // New instruction
  iq_entry_t new_instr, issued_instr;

  // ----------------
  // ISSUE QUEUE FIFO
  // ----------------
  // Assemble new queue entry with the data from the fetch unit
  assign new_instr.curr_pc       = curr_pc_i;
  assign new_instr.instruction   = instruction_i;
  assign new_instr.pred_target   = pred_target_i;
  assign new_instr.pred_taken    = pred_taken_i;
  assign new_instr.except_raised = except_raised_i;
  assign new_instr.except_code   = except_code_i;

  fifo #(
    .DATA_T(iq_entry_t),
    .DEPTH (len5_config_pkg::IQ_DEPTH)
  ) u_issue_fifo (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .flush_i(flush_i),
    .valid_i(fetch_valid_i),
    .ready_i(issue_ready_i),
    .valid_o(issue_valid_o),
    .ready_o(fetch_ready_o),
    .data_i (new_instr),
    .data_o (issued_instr)
  );

  // Output instruction
  // ------------------
  assign curr_pc_o       = issued_instr.curr_pc;
  assign instruction_o   = issued_instr.instruction;
  assign pred_target_o   = issued_instr.pred_target;
  assign pred_taken_o    = issued_instr.pred_taken;
  assign except_raised_o = issued_instr.except_raised;
  assign except_code_o   = issued_instr.except_code;

endmodule

