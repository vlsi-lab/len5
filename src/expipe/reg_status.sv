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
// File: reg_status.sv
// Author: Michele Caon
// Date: 12/11/2019

module reg_status 
    import expipe_pkg::*;
#( 
    REG_NUM = 32,
    REG_IDX_LEN = 5
) 
(
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,
	//input   logic					stall,

    // Handshake from/to the issue logic
    input   logic                   issuel_valid_i,
    output  logic                   issuel_ready_o,

    // Data from/to the issue logic
    input   logic [REG_IDX_LEN-1:0] issue_rd_idx_i,         // destination register of the issuing instruction
    input   logic [ROB_IDX_LEN-1:0] issue_rob_idx_i,  // ROB index where the instruction is being allocated (tail pointer of the ROB)

    input   logic [REG_IDX_LEN-1:0] issue_rs1_idx_i,        // first source register index
    input   logic [REG_IDX_LEN-1:0] issue_rs2_idx_i,        // second source register index
    output  logic                   issue_rs1_busy_o,       // rs1 value is in the ROB or has to be computed
    output  logic [ROB_IDX_LEN-1:0] issue_rs1_rob_idx_o,    // the index of the ROB where the result is found
    output  logic                   issue_rs2_busy_o,       // rs1 value is in the ROB or has to be computed
    output  logic [ROB_IDX_LEN-1:0] issue_rs2_rob_idx_o,    // the index of the ROB where the result is found

    // Handshake from/to the commit logic
    input   logic                   comm_valid_i,
    output  logic                   comm_ready_o,

    // Data from the commit logic
    input   logic [REG_IDX_LEN-1:0] comm_rd_idx_i,          // destination register of the committing instr.
    input   logic [ROB_IDX_LEN-1:0] comm_head_idx_i         // head entry of the ROB
);

    // DEFINITIONS

    // Register status data
    regstat_entry_t                 regstat_data [0:REG_NUM-1];

    // Operation control
    logic                           regstat_issue_upd, regstat_comm_upd;

    //-----------------------------------------\\
    //----- REGISTER STATUS CONTROL LOGIC -----\\
    //-----------------------------------------\\
    always_comb begin: regstat_control_logic
        // DEFAULT VALUES:
        regstat_issue_upd           = 1'b0;
        regstat_comm_upd            = 1'b0;

        // ISSUING INSTRUCTION
        if (issuel_valid_i) begin
            regstat_issue_upd       =1'b1;
        end

        // COMMITTING INSTRUCTION
        // Only if the committing instruction is the last one writing the register the update is performed
        if (comm_valid_i) begin
            if (comm_head_idx_i == regstat_data[comm_rd_idx_i].rob_idx) begin
                regstat_comm_upd        = 1'b1;
            end
        end
    end

    //---------------------------------------\\
    //----- REGISTER STATUS DATA UPDATE -----\\
    //---------------------------------------\\
    always_ff @(posedge clk_i or negedge rst_n_i) begin: rs_data_update
        if (!rst_n_i) begin // Asynchronous reset
            foreach (regstat_data[i]) begin
                regstat_data[i]                 <= 0;
            end
        end else if (flush_i) begin // Synchronous flush: clearing status info is enough
            foreach (regstat_data[i]) begin // Synchronous clear
                regstat_data[i]                 <= 0;
            end
        end else begin // Normal update 

            // WRITE DESTINATION ROB ENTRY FROM ISSUE STAGE (WRITE PORT 1)
            // The ROB entry assigned to the issuing instructioin (tail of the ROB) is recorded in the corresponding destination register entry
            if (regstat_issue_upd/*&& !(stall)*/) begin
                regstat_data[issue_rd_idx_i].busy           += 1'b1;            // a new in-flight instruction is writing rd
                regstat_data[issue_rd_idx_i].rob_idx        <= issue_rob_idx_i; // rd value will be available in this ROB entry
            end

            // CLEAR REGISTER INFORMATION WHEN AN INSTRUCTION COMMITS (WRITE PORT 2)
            // When an instruction commits from the ROB, its result may be written back to the register file. In this case, the busy counter is decremented. If this counter is zero, an issuing instr. sourcing one of its operand from this register can find the operand in the register file
            if (regstat_comm_upd/*&& !(stall)*/) begin
                regstat_data[comm_rd_idx_i].busy -= 1'b0;   // one less in-flight instruction will write rd
            end
        end
    end

    //--------------------------------------\\
    //----- REGISTER STATUS READ PORTS -----\\
    //--------------------------------------\\
    // READ OPERANDS FOR THE ISSUE STAGE 
    // rs1 (READ PORT 1)
    assign issue_rs1_busy_o             = |regstat_data[issue_rs1_idx_i].busy;      // 0 only if no in-flight instructions will write that register
    assign issue_rs1_rob_idx_o          = regstat_data[issue_rs1_idx_i].rob_idx;
    // rs2 (READ PORT 2)
    assign issue_rs2_busy_o             = |regstat_data[issue_rs2_idx_i].busy;      // 0 only if no in-flight instructions will write that register
    assign issue_rs2_rob_idx_o          = regstat_data[issue_rs2_idx_i].rob_idx;

    //---------------------------------------\\
    //----- OUTPUT HANDSHAKE GENERATION -----\\
    //---------------------------------------\\
    // The register status data structure is always ready to accept requests from both the issue stage and the commit stage
    assign issuel_ready_o                = 1'b1;
    assign comm_ready_o                 = 1'b1;
    
endmodule
