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

import len5_pkg::XLEN;
import len5_pkg::XREG_NUM;
import len5_pkg::REG_IDX_LEN;
import expipe_pkg::*;

module int_rf 
(
    input   logic                   clk_i,
    input   logic                   rst_n_i,

    // Handshake from the commit logic 
    input   logic                   comm_valid_i,
    output  logic                   comm_ready_o,

    // Data from the commit logic (result write port)
    input   logic [REG_IDX_LEN-1:0] comm_rd_idx_i,
    input   logic [XLEN-1:0]        comm_rd_value_i,

    // Data to the issue stage (operands read ports)
    input   logic [REG_IDX_LEN-1:0] issue_rs1_idx_i,
    input   logic [REG_IDX_LEN-1:0] issue_rs2_idx_i,
    output  logic [XLEN-1:0]        issue_rs1_value_o,
    output  logic [XLEN-1:0]        issue_rs2_value_o
);

    // DEFINITIONS

    // Register file data
    logic [XLEN-1:0] rf_data [0:XREG_NUM-1];

    //------------------------------------\\
    //----- REGISTER FILE WRITE PORT -----\\
    //------------------------------------\\
    // Synchronous write
    always_ff @(posedge clk_i or negedge rst_n_i) begin: res_write_port
        if (!rst_n_i) begin // Asynchronous reset
            rf_data[0] <= 0; // hard-wired x0
            for (int i = 1; i < XREG_NUM; i++) begin
                rf_data[i]                  <= 0;
            end
        end else begin
            rf_data[0] <= 0; // hard-wired x0
            if (comm_valid_i && (comm_rd_idx_i != 0)) begin // if the data from the commit stage is valid, update the RF
                rf_data[comm_rd_idx_i]      <= comm_rd_value_i;
            end
        end
    end

    //------------------------------------\\
    //----- REGISTER FILE READ PORTS -----\\
    //------------------------------------\\
    // Asynchronous read
    always_comb begin: operands_read_ports
        // READ PORT 1 (rs1)
        issue_rs1_value_o                   = rf_data[issue_rs1_idx_i];
        // READ PORT 2 (rs2)
        issue_rs2_value_o                   = rf_data[issue_rs2_idx_i];
    end

    //---------------------\\
    //----- READY OUT -----\\
    //---------------------\\
    // Always ready to accept data
    assign comm_ready_o                     = 1'b1;
    
endmodule
