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
// File: cdb.sv
// Author: Michele Caon
// Date: 11/11/2019

import expipe_pkg::*;
import len5_pkg::XLEN;

module cdb 
(
    input   logic               clk_i,
    input   logic               rst_n_i,
    input   logic               flush_i,
	//input logic stall,

    // Handshake from/to the maximum priority EU
    input   logic               max_prio_valid_i,
    output  logic               max_prio_ready_o,

    // Data from the maximum priority EU
    input   var cdb_data_t          max_prio_data_i,
	output  cdb_data_t          max_prio_data_o,

    // Handshake from/to the reservation stations
    input   logic [0:EU_N-2]    rs_valid_i, 
    output  logic [0:EU_N-2]    rs_ready_o,

    // Data from the reservation stations or issue queue.
    input   var cdb_data_t          rs_data_i[0:EU_N-2],
	output  cdb_data_t          rs_data_o[0:EU_N-2],

	//new added
	// Handshake from/to the IQL
	output   logic                       cdb_valid_i,
	input  logic                         cdb_ready_o,

	// Data to the IQL
	output   logic                       cdb_except_raised_i,
	output   logic [XLEN-1:0]            cdb_value_i,
	output   logic [ROB_IDX_LEN-1:0]	 cdb_rob_idx_i,
	//To here

    // Handshake from/to the ROB
    input   logic               rob_ready_i,
    output  logic               rob_valid_o,

    // Data to the ROB
    output  cdb_data_t          rob_data_o
);

	
    // DEFINITIONS  
	logic                       rob_valid_k;
	//cdb_rob_idx_i = rob_idx;
    //cdb_value_i   = value;
    //cdb_except_raised_i =   except_raised; 

    // CDB MUX
    cdb_data_t                  low_prio_mux_data;
	//cdb_data_t      [0:EU_N-2]    temp;

    // Served unit index
    logic                       served_max_prio;
    logic [$clog2(EU_N)-1:0]    served;

    // -----------
    // CDB ARBITER
    // -----------
    cdb_arbiter u_cdb_arbiter
    (
        .clk_i              (clk_i),
        .rst_n_i            (rst_n_i),
        .flush_i            (flush_i),
		//.stall(stall),

        // Handshake from/to the maximum priority unit
        .max_prio_valid_i   (max_prio_valid_i),
        .max_prio_ready_o   (max_prio_ready_o),

        // Handshake from/to the units
        .valid_i            (rs_valid_i),
        .ready_o            (rs_ready_o),

        // Handshake from/to the ROB
        .rob_ready_i        (rob_ready_i),
        .rob_valid_o        (rob_valid_k),

        // Served unit
        .served_max_prio_o  (served_max_prio),
        .served_o           (served)
    );

	assign rob_valid_o = rob_valid_k;
	assign cdb_valid_i = rob_valid_k;

    // -------
    // CDB MUX
    // -------
    // Max priority MUX
    assign rob_data_o = (served_max_prio) ? max_prio_data_i : low_prio_mux_data;
    
    // Low priority MUX
    assign low_prio_mux_data = rs_data_i[served-1]; // TODO: fixed indexing
	//assign temp = rs_data_i;
	//assign rs_data_o[served] = rs_data_i[served]; // temp[served];
	assign rs_data_o = rs_data_i; // temp[served];
	assign max_prio_data_o =  max_prio_data_i;
//New
	assign cdb_rob_idx_i = rob_data_o.rob_idx;
    assign cdb_value_i   = rob_data_o.value;
    assign cdb_except_raised_i =   rob_data_o.except_raised; 

    
endmodule
