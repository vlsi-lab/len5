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
// File: branch_unit.sv
// Author: Michele Caon
// Date: 17/11/2021

import len5_pkg::*;
import expipe_pkg::*;

module branch_unit 
#(
    RS_DEPTH = 4  // must be a power of 2
)
(
    input   logic                           clk_i,
    input   logic                           rst_n_i,
    input   logic                           flush_i,

    // Handshake from/to issue logic
    input   logic                           issue_valid_i,
    output  logic                           issue_ready_o,

    // Data from the decode stage
    input   branch_type_t                   branch_type_i,
    input   logic                           rs1_ready_i,
    input   rob_idx_t                       rs1_idx_i,
    input   logic [XLEN-1:0]                rs1_value_i,
    input   logic                           rs2_ready_i,
    input   rob_idx_t                       rs2_idx_i,
    input   logic [XLEN-1:0]                rs2_value_i,
    input   logic [XLEN-1:0]                imm_value_i,
    input   rob_idx_t                       dest_idx_i,
    input   logic [XLEN-1:0]                curr_pc_i,
    input   logic [XLEN-1:0]                pred_target_i,
    input   logic                           pred_taken_i,

    // Hanshake from/to the CDB 
    input   logic                           cdb_ready_i,
    input   logic                           cdb_valid_i,        // to know if the CDB is carrying valid data
    output  logic                           cdb_valid_o,

    // Data from/to the CDB
    input   cdb_data_t                      cdb_data_i,
    output  cdb_data_t                      cdb_data_o
);

    // Data from/to the execution unit
    logic [XLEN-1:0]        rs_bu_rs1;
    logic [XLEN-1:0]        rs_bu_rs2;
    logic [XLEN-1:0]        rs_bu_imm;
    logic [XLEN-1:0]        rs_bu_curr_pc;
    logic [XLEN-1:0]        rs_bu_pred_target;
    logic                   rs_bu_pred_taken;
    logic [BU_CTL_LEN-1:0]  rs_bu_branch_type;
    logic                   bu_rs_res_mispredict;

    // Beanch logic <--> Reservation Station
    logic                           bu_rs_ready;
    logic                           bu_rs_valid;
    logic                           rs_bu_valid;
    logic                           rs_bu_ready;
    logic [$clog2(RS_DEPTH)-1:0]    rs_bu_entry_idx;

    // Branch logic
    logic                   res_taken;
    logic                   wrong_taken;
    logic                   wrong_target;
    logic                   res_mispredicted;
    logic [XLEN-1:0]        res_target; 

    // Branch logic output register
        // Branch logic output register data type
    typedef struct packed {
        logic [$clog2(RS_DEPTH)-1:0]    entry_idx;
        logic                           res_mispredicted;
        logic                           res_taken;
        logic [XLEN-1:0]                res_target;
    } bu_out_reg_t;
    bu_out_reg_t            bu_outreg_in, bu_outreg_out;

    // ------------
    // BRANCH LOGIC
    // ------------

    // Branch taken detection logic
    always_comb begin
        case (rs_bu_branch_type)
        BEQ:      res_taken = (rs_bu_rs1 == rs_bu_rs2);
        BNE:      res_taken = (rs_bu_rs1 != rs_bu_rs2);
        BLT:      res_taken = ($signed(rs_bu_rs1) < $signed(rs_bu_rs2));
        BGE:      res_taken = ($signed(rs_bu_rs1) >= $signed(rs_bu_rs2));
        BLTU:     res_taken = (rs_bu_rs1 < rs_bu_rs2);
        BGEU:     res_taken = (rs_bu_rs1 >= rs_bu_rs2);
        JUMP:     res_taken = 1'b1;
        default:  res_taken = 1'b0;
        endcase
    end
    
    // Target adder
    assign  res_target  = rs_bu_imm + rs_bu_curr_pc; // correct target address

    // Misprediction logic
    assign  wrong_target        = rs_bu_pred_target != res_target;
    assign  wrong_taken         = rs_bu_pred_taken != res_taken;
    assign  res_mispredicted    = wrong_taken | wrong_target;

    // Branch logic output register
    // NOTE: skipped by default, since it's likely not on the critical path
    assign  bu_outreg_in.entry_idx          = rs_bu_entry_idx;
    assign  bu_outreg_in.res_mispredicted   = res_mispredicted;
    assign  bu_outreg_in.res_taken          = res_taken;
    assign  bu_outreg_in.res_target         = res_target;
    spill_cell #(
        .DATA_T (bu_out_reg_t),
        .SKIP   (1           )
    ) u_bu_out_reg (
    	.clk_i   (clk_i         ),
        .rst_n_i (rst_n_i       ),
        .valid_i (rs_bu_valid   ),
        .ready_i (rs_bu_ready   ),
        .valid_o (bu_rs_valid   ),
        .ready_o (bu_rs_ready   ),
        .data_i  (bu_outreg_in  ),
        .data_o  (bu_outreg_out )
    );

    // -------------------------------
    // BRANCH UNIT RESERVATION STATION
    // -------------------------------
    branch_rs #(
        .RS_DEPTH   (RS_DEPTH   )
    ) u_branch_rs(
    	.clk_i              (clk_i                          ),
        .rst_n_i            (rst_n_i                        ),
        .flush_i            (flush_i                        ),
        .issue_valid_i      (issue_valid_i                  ),
        .issue_ready_o      (issue_ready_o                  ),
        .branch_type_i      (branch_type_i                  ),
        .rs1_ready_i        (rs1_ready_i                    ),
        .rs1_idx_i          (rs1_idx_i                      ),
        .rs1_value_i        (rs1_value_i                    ),
        .rs2_ready_i        (rs2_ready_i                    ),
        .rs2_idx_i          (rs2_idx_i                      ),
        .rs2_value_i        (rs2_value_i                    ),
        .imm_value_i        (imm_value_i                    ),
        .dest_idx_i         (dest_idx_i                     ),
        .curr_pc_i          (curr_pc_i                      ),
        .pred_target_i      (pred_target_i                  ),
        .pred_taken_i       (pred_taken_i                   ),
        .bu_ready_i         (bu_rs_ready                    ),
        .bu_valid_i         (bu_rs_valid                    ),
        .bu_valid_o         (rs_bu_valid                    ),
        .bu_ready_o         (rs_bu_ready                    ),
        .bu_entry_idx_i     (bu_outreg_out.entry_idx        ),
        .bu_res_mis_i       (bu_outreg_out.res_mispredicted ),
        .bu_res_taken_i     (bu_outreg_out.res_taken        ),
        .bu_res_target_i    (bu_outreg_out.res_target       ),
        .bu_entry_idx_o     (rs_bu_entry_idx                ),
        .bu_rs1_o           (rs_bu_rs1                      ),
        .bu_rs2_o           (rs_bu_rs2                      ),
        .bu_imm_o           (rs_bu_imm                      ),
        .bu_curr_pc_o       (rs_bu_curr_pc                  ),
        .bu_pred_target_o   (rs_bu_pred_target              ),
        .bu_pred_taken_o    (rs_bu_pred_taken               ),
        .bu_branch_type_o   (rs_bu_branch_type              ),
        .cdb_ready_i        (cdb_ready_i                    ),
        .cdb_valid_i        (cdb_valid_i                    ),
        .cdb_valid_o        (cdb_valid_o                    ),
        .cdb_data_i         (cdb_data_i                     ),
        .cdb_data_o         (cdb_data_o                     )
    );

endmodule
