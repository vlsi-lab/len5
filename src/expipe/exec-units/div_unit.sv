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
// File: div_unit.sv
// Author: Michele Caon
// Date: 17/11/2021

import len5_pkg::*;
import expipe_pkg::*;

module div_unit 
#(
    RS_DEPTH = 4, // must be a power of 2,
    
    // EU-specific parameters
    EU_CTL_LEN = 4
)
(
    // Clock, reset, and flush
    input   logic                   clk_i,
    input   logic                   rst_n_i,
    input   logic                   flush_i,

    // Issue stage
    input   logic                   issue_valid_i,
    output  logic                   issue_ready_o,
    input   div_ctl_t               issue_eu_ctl_i,
    input   op_data_t               issue_rs1_i,
    input   op_data_t               issue_rs2_i,
    input   rob_idx_t               issue_dest_rob_idx_i,

    // CDB 
    input   logic                   cdb_ready_i,
    input   logic                   cdb_valid_i,        // to know if the CDB is carrying valid data
    output  logic                   cdb_valid_o,
    input   cdb_data_t              cdb_data_i,
    output  cdb_data_t              cdb_data_o
);

    // Divider handshaking
    logic                   rs_div_valid;
    logic                   rs_div_ready;
    logic                   div_rs_valid;
    logic                   div_rs_ready;

    // Data from/to the execution unit
    logic [$clog2(RS_DEPTH)-1:0] rs_div_entry_idx;
    logic [EU_CTL_LEN-1:0]  rs_div_ctl;
    logic [XLEN-1:0]        rs_div_rs1_value;
    logic [XLEN-1:0]        rs_div_rs2_value;
    logic [$clog2(RS_DEPTH)-1:0] div_rs_entry_idx;
    logic [XLEN-1:0]        div_rs_result;
    logic                   div_rs_except_raised;
    except_code_t           div_rs_except_code;

    // DIV reservation station
    // -----------------------
    arith_rs #(
        .DEPTH      (RS_DEPTH   ),
        .EU_CTL_LEN (EU_CTL_LEN )
    ) u_div_rs (
    	.clk_i                (clk_i                ),
        .rst_n_i              (rst_n_i              ),
        .flush_i              (flush_i              ),
        .issue_valid_i        (issue_valid_i        ),
        .issue_ready_o        (issue_ready_o        ),
        .issue_eu_ctl_i       (issue_eu_ctl_i       ),
        .issue_rs1_i          (issue_rs1_i          ),
        .issue_rs2_i          (issue_rs2_i          ),
        .issue_dest_rob_idx_i (issue_dest_rob_idx_i ),
        .cdb_ready_i          (cdb_ready_i          ),
        .cdb_valid_i          (cdb_valid_i          ),
        .cdb_valid_o          (cdb_valid_o          ),
        .cdb_data_i           (cdb_data_i           ),
        .cdb_data_o           (cdb_data_o           ),
        .eu_ready_i           (div_rs_ready         ),
        .eu_valid_i           (div_rs_valid         ),
        .eu_valid_o           (rs_div_valid         ),
        .eu_ready_o           (rs_div_ready         ),
        .eu_entry_idx_i       (div_rs_entry_idx     ),
        .eu_result_i          (div_rs_result        ),
        .eu_except_raised_i   (div_rs_except_raised ),
        .eu_except_code_i     (div_rs_except_code   ),
        .eu_ctl_o             (rs_div_ctl           ),
        .eu_rs1_o             (rs_div_rs1_value     ),
        .eu_rs2_o             (rs_div_rs2_value     ),
        .eu_entry_idx_o       (rs_div_entry_idx     )
    );

    div #(.EU_CTL_LEN (EU_CTL_LEN), .RS_DEPTH (RS_DEPTH)) u_div
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
        .eu_entry_idx_o (eu_entry_idx_o)
    );

endmodule
