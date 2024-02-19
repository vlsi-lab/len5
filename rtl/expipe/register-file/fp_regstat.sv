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
// File: fp_regstat.sv
// Author: Michele Caon
// Date: 12/11/2019

/*
 * NOTE: ADD RS3!
 */

module fp_regstat #(
  parameter  int unsigned REG_NUM   = 32,              // power of 2
  // Dependent parameters: do NOT override
  localparam int unsigned RegIdxLen = $clog2(REG_NUM)
) (
  input logic clk_i,
  input logic rst_ni,

  // Handshake from/to the issue logic
  input logic issue_valid_i,

  // Data from/to the issue logic
  input logic [RegIdxLen-1:0] issue_rd_idx_i,  // destination register of the issuing instruction
  input expipe_pkg::rob_idx_t issue_rob_idx_i,  // allocated ROB index

  input logic [RegIdxLen-1:0] issue_rs1_idx_i,  // first source register index
  input logic [RegIdxLen-1:0] issue_rs2_idx_i,  // second source register index
  output logic issue_rs1_busy_o,  // rs1 value is in the ROB or has to be computed
  output expipe_pkg::rob_idx_t issue_rs1_rob_idx_o,  // the index of the ROB where the result is found
  output logic issue_rs2_busy_o,  // rs1 value is in the ROB or has to be computed
  output expipe_pkg::rob_idx_t issue_rs2_rob_idx_o,  // the index of the ROB where the result is found

  // Handshake from/to the commit logic
  input logic comm_valid_i,

  // Data from the commit logic
  input logic [RegIdxLen-1:0] comm_rd_idx_i,  // destination register of the committing instr.
  input expipe_pkg::rob_idx_t comm_head_idx_i  // head entry of the ROB
);

  import expipe_pkg::*;
  // DEFINITIONS

  // Register status data
  regstat_entry_t regstat_data[REG_NUM];  /* TODO: check for error on this */

  // Operation control
  logic regstat_issue_upd, regstat_comm_upd;

  // -----------------------------
  // REGISTER STATUS CONTROL LOGIC
  // -----------------------------
  always_comb begin : regstat_control_logic
    // DEFAULT VALUES:
    regstat_issue_upd = 1'b0;
    regstat_comm_upd  = 1'b0;

    // ISSUING INSTRUCTION
    if (issue_valid_i) begin
      regstat_issue_upd = 1'b1;
    end

    // COMMITTING INSTRUCTION
    // Only if the committing instruction is the last one writing the register the update is performed
    if (comm_valid_i) begin
      if (comm_head_idx_i == regstat_data[comm_rd_idx_i].rob_idx) begin
        regstat_comm_upd = 1'b1;
      end

      // Earlier
      // if (comm_head_idx_i == regstat_data[comm_rd_idx_i].rob_idx && issue_rs1_idx_i !=comm_rd_idx_i && issue_rs2_idx_i !=comm_rd_idx_i) begin /* TODO: remove from '&& issue_rs1_idx_i !=comm_rd_idx_i '&& issue_rs2_idx_i !=comm_rd_idx_i' */
      //     regstat_comm_upd        = 1'b1;
      // end
    end
  end

  // ---------------------------
  // REGISTER STATUS DATA UPDATE
  // ---------------------------
  always_ff @(posedge clk_i or negedge rst_ni) begin : rs_data_update
    if (!rst_ni) begin  // Asynchronous reset
      foreach (regstat_data[i]) begin
        regstat_data[i] <= 0;
      end
    end else begin  // Normal update

      // WRITE DESTINATION ROB ENTRY FROM ISSUE STAGE (WRITE PORT 1)
      // The ROB entry assigned to the issuing instructioin (tail of the ROB) is recorded in the corresponding destination register entry
      if (regstat_issue_upd) begin
        regstat_data[issue_rd_idx_i].busy += 1'b1;  // a new in-flight instruction is writing rd
        regstat_data[issue_rd_idx_i].rob_idx <= issue_rob_idx_i;  // rd value will be available in this ROB entry
      end

      // CLEAR REGISTER INFORMATION WHEN AN INSTRUCTION COMMITS (WRITE PORT 2)
      // When an instruction commits from the ROB, its result may be written back to the register file. In this case, the busy counter is decremented. If this counter is zero, an issuing instr. sourcing one of its operand from this register can find the operand in the register file
      if (regstat_comm_upd) begin
        regstat_data[comm_rd_idx_i].busy -= 1'b0;  // one less in-flight instruction will write rd

        //regstat_data[comm_rd_idx_i].busy <= 1'b0;
      end
    end
  end

  // --------------------------
  // REGISTER STATUS READ PORTS
  // --------------------------
  // READ OPERANDS FOR THE ISSUE STAGE
  // rs1 (READ PORT 1)
  assign issue_rs1_busy_o    = |regstat_data[issue_rs1_idx_i].busy;  // 0 only if written by in-flight instruction

  //assign issue_rs1_busy_o             = regstat_data[issue_rs1_idx_i].busy;
  assign issue_rs1_rob_idx_o = regstat_data[issue_rs1_idx_i].rob_idx;
  // rs2 (READ PORT 2)
  assign issue_rs2_busy_o    = |regstat_data[issue_rs2_idx_i].busy;  // 0 only if written by in-flight instruction

  //assign issue_rs2_busy_o             = regstat_data[issue_rs2_idx_i].busy;
  assign issue_rs2_rob_idx_o = regstat_data[issue_rs2_idx_i].rob_idx;

  // ---------------------------
  // OUTPUT HANDSHAKE GENERATION
  // ---------------------------
  // The register status data structure is always ready to accept requests from both the issue stage and the commit stage
  // assign issue_ready_o                = 1'b1;
  // assign comm_ready_o                 = 1'b1;

endmodule
