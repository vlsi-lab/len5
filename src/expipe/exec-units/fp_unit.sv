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
// File: fp_unit.sv
// Author: Michele Caon
// Date: 17/11/2021

import len5_pkg::*;
import expipe_pkg::*;
import csr_pkg::FCSR_FRM_LEN;

module fp_unit 
#(
    RS_DEPTH = 4, // must be a power of 2,
    
    // EU-specific parameters
    EU_CTL_LEN = 4,
    EXCEPT_LEN = 2
)
(
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,
	

    // Handshake from/to issue logic
    input   logic                   issue_valid_i,
    output  logic                   issue_ready_o,

    // Data from the issue stage
    input   logic [EU_CTL_LEN-1:0]  eu_ctl_i,
    input   logic                   rs1_ready_i,
    input   rob_idx_t rs1_idx_i,
    input   logic [XLEN-1:0]        rs1_value_i,
    input   logic                   rs2_ready_i,
    input   rob_idx_t rs2_idx_i,          
    input   logic [XLEN-1:0]        rs2_value_i,        // can contain immediate for I type instructions
    input   rob_idx_t dest_idx_i,

    // Hanshake from/to the CDB 
    input   logic                   cdb_ready_i,
    input   logic                   cdb_valid_i,        // to know if the CDB is carrying valid data
    output  logic                   cdb_valid_o,

    // Data from/to the CDB
    input   rob_idx_t cdb_idx_i,
    input   logic [XLEN-1:0]        cdb_data_i,
    input   logic                   cdb_except_raised_i,
    output  rob_idx_t cdb_idx_o,
    output  logic [XLEN-1:0]        cdb_data_o,
    output  logic                   cdb_except_raised_o,
    output  except_code_t cdb_except_o,

    // CSR data
    input   logic [FCSR_FRM_LEN-1:0] csr_frm_i
);

    // Handshake from/to the execution unit
    logic                   eu_ready_i;
    logic                   eu_valid_i;
    logic                   eu_valid_o;
    logic                   eu_ready_o;

    // Data from/to the execution unit
    logic [$clog2(RS_DEPTH)-1:0] eu_entry_idx_i;
    logic [XLEN-1:0]        eu_result_i;
    logic                   eu_except_raised_i;
    logic [EXCEPT_LEN-1:0]  eu_except_code_i;
    logic [EU_CTL_LEN-1:0]  eu_ctl_o;
    logic [XLEN-1:0]        eu_rs1_o;
    logic [XLEN-1:0]        eu_rs2_o;
    logic [$clog2(RS_DEPTH)-1:0] eu_entry_idx_o;

generic_rs #(.EU_CTL_LEN (EU_CTL_LEN), .RS_DEPTH (RS_DEPTH), .EXCEPT_LEN(2)) u_fpu_generic_rs
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	
    .issue_valid_i (issue_valid_i),
    .issue_ready_o (issue_ready_o),
    .eu_ctl_i (eu_ctl_i),
    .rs1_ready_i (rs1_ready_i),
    .rs1_idx_i (rs1_idx_i),
    .rs1_value_i (rs1_value_i),
    .rs2_ready_i (rs2_ready_i),
    .rs2_idx_i (rs2_idx_i),
    .rs2_value_i (rs2_value_i),
    .dest_idx_i (dest_idx_i),
    .eu_ready_i (eu_ready_i),
    .eu_valid_i (eu_valid_i),
    .eu_valid_o (eu_valid_o),
    .eu_ready_o (eu_ready_o),
    .eu_entry_idx_i (eu_entry_idx_i),
    .eu_result_i (eu_result_i),
    .eu_except_raised_i (eu_except_raised_i),
    .eu_except_code_i (eu_except_code_i),
    .eu_ctl_o (eu_ctl_o),
    .eu_rs1_o (eu_rs1_o),
    .eu_rs2_o (eu_rs2_o),
    .eu_entry_idx_o (eu_entry_idx_o), 
    .cdb_ready_i (cdb_ready_i),
    .cdb_valid_i (cdb_valid_i),
    .cdb_valid_o (cdb_valid_o),
    .cdb_idx_i (cdb_idx_i),
    .cdb_data_i (cdb_data_i),
    .cdb_except_raised_i (cdb_except_raised_i),
    .cdb_idx_o (cdb_idx_o),
    .cdb_data_o (cdb_data_o),
    .cdb_except_raised_o (cdb_except_raised_o),
    .cdb_except_o (cdb_except_o)
);

fpu #(.EU_CTL_LEN (EU_CTL_LEN), .RS_DEPTH (RS_DEPTH), .EXCEPT_LEN(2)) u_fpu
(
    .clk_i (clk_i),
    .rst_n_i (rst_n_i),
    .flush_i (flush_i),
	.eu_ready_i (eu_ready_i),
    .eu_valid_i (eu_valid_i),
    .eu_valid_o (eu_valid_o),
    .eu_ready_o (eu_ready_o),
    .eu_entry_idx_i (eu_entry_idx_i),
    .eu_result_i (eu_result_i),
    .eu_except_raised_i (eu_except_raised_i),
    .eu_except_code_i (eu_except_code_i),
    .eu_ctl_o (eu_ctl_o),
    .eu_rs1_o (eu_rs1_o),
    .eu_rs2_o (eu_rs2_o),
    .eu_entry_idx_o (eu_entry_idx_o),
    .csr_frm_i(csr_frm_i)
);

endmodule
