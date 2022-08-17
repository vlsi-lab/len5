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
// File: datapath.sv
// Author: Michele Caon
// Date: 19/11/2021

import len5_pkg::*;
import memory_pkg::*;
import fetch_pkg::*;
import csr_pkg::csr_priv_t;

module datapath #(
    parameter PC_GEN_BOOT_PC = 64'h0,
    parameter BPU_HISTORY_LEN = 4,
    parameter BPU_BTB_BITS = 4
) (
    // Clock and reset
    input   logic               clk_i,
    input   logic               rst_n_i,

    // Datapath <--> memory emulator
    input   logic               mem_valid_i,
    input   logic               mem_ready_i,
    output  logic               mem_valid_o,
    output  logic               mem_ready_o,
    input   mem_ans_t           mem_ans_i,
    output  mem_req_t           mem_req_o          
);

    // ----------------
    // INTERNAL SIGNALS
    // ----------------

    // Frontend <--> backend
    // ---------------------
    logic               fe_be_valid;
    logic               be_fe_ready;
    logic [ILEN-1:0]    fe_be_instr;
    prediction_t        fe_be_pred;
    logic               fe_be_except_raised;
    except_code_t       fe_be_except_code;
    logic               be_fe_bpu_flush;
    logic               be_fe_res_valid;
    resolution_t        be_fe_res;
    logic               be_fe_except_raised;
    logic [XLEN-1:0]    be_fe_except_pc;

    // Frontend <--> Memory Arbiter
    // ----------------------------
    logic               fe_mem_valid;
    logic               mem_fe_ready;
    mem_req_t           fe_mem_req;
    logic               mem_fe_valid;
    logic               fe_mem_ready;

    // Backend <--> Mmeory Arbiter
    // ---------------------------
    logic               be_mem_valid;
    logic               mem_be_ready;
    mem_req_t           be_mem_req;
    logic               mem_be_valid;
    logic               be_mem_ready;

    // ---------
    // FRONT-END
    // ---------

    fetch_stage #(
        .HLEN     (BPU_HISTORY_LEN ),
        .BTB_BITS (BPU_BTB_BITS    ),
        .BOOT_PC  (PC_GEN_BOOT_PC  )
    ) u_fetch_stage (
    	.clk_i                 (clk_i                 ),
        .rst_n_i               (rst_n_i               ),
        .flush_i               (flush_i               ),
        .flush_bpu_i           (be_fe_bpu_flush       ),
        .mem_valid_i           (mem_fe_valid          ),
        .mem_ready_i           (mem_fe_ready          ),
        .mem_valid_o           (fe_mem_valid          ),
        .mem_ready_o           (fe_mem_ready          ),
        .mem_ans_i             (mem_ans_i             ),
        .mem_req_o             (fe_mem_req            ),
        .issue_ready_i         (be_fe_ready           ),
        .issue_valid_o         (fe_be_valid           ),
        .issue_instr_o         (fe_be_instr           ),
        .issue_pred_o          (fe_be_pred            ),
        .issue_except_raised_o (fe_be_except_raised   ),
        .issue_except_code_o   (fe_be_except_code     ),
        .comm_except_raised_i  (be_fe_except_raised   ),
        .comm_except_pc_i      (be_fe_except_pc       ),
        .comm_res_valid_i      (be_fe_res_valid       ),
        .comm_res_i            (be_fe_res             )
    );

    // --------
    // BACK-END
    // --------

    backend u_backend(
    	.clk_i                 (clk_i                 ),
        .rst_n_i               (rst_n_i               ),
        .fetch_valid_i         (fe_be_valid           ),
        .fetch_ready_o         (be_fe_ready           ),
        .fetch_instr_i         (fe_be_instr           ),
        .fetch_pred_i          (fe_be_pred            ),
        .fetch_except_raised_i (fe_be_except_raised   ),
        .fetch_except_code_i   (fe_be_except_code     ),
        .fetch_bpu_flush_o     (be_fe_bpu_flush       ),
        .fetch_res_valid_o     (be_fe_res_valid       ),
        .fetch_res_o           (be_fe_res             ),
        .fetch_except_raised_o (be_fe_except_raised   ),
        .fetch_except_pc_o     (be_fe_except_pc       ),
        .mem_valid_i           (mem_be_valid          ),
        .mem_ready_i           (mem_be_ready          ),
        .mem_valid_o           (be_mem_valid          ),
        .mem_ready_o           (be_mem_ready          ),
        .mem_req_o             (be_mem_req            ),
        .mem_ans_i             (mem_ans_i             )
    );

    // -------------
    // MEMORY-SYSTEM
    // -------------
    // NOTE: in the bare-metal version, the load-store unit is directly
    //       connected to the memory.

    // MEMORY REQUEST ARBITER
    // ----------------------
    prio_2way_arbiter #(
        .DATA_T (mem_req_t )
    ) u_mem_req_arbiter (
        .high_prio_valid_i (fe_mem_valid  ),
        .low_prio_valid_i  (be_mem_valid  ),
        .ready_i           (mem_ready_i   ),
        .valid_o           (mem_valid_o   ),
        .high_prio_ready_o (mem_fe_ready  ),
        .low_prio_ready_o  (mem_be_ready  ),
        .high_prio_data_i  (fe_mem_req    ),
        .low_prio_data_i   (be_mem_req    ),
        .data_o            (mem_req_o     )
    );

    // MEMORY ANSWER DECODER
    // ---------------------
    always_comb begin : mem_ans_decoder
        mem_fe_valid    = 1'b0;
        mem_be_valid    = 1'b0;
        mem_ready_o     = 1'b0;

        if (mem_valid_i) begin
            if (mem_ans_i.acc_type == MEM_ACC_INSTR) begin
                mem_fe_valid    = 1'b1;
                mem_ready_o     = fe_mem_ready;
            end else begin
                mem_be_valid    = 1'b1;
                mem_ready_o     = be_mem_ready;
            end
        end
    end
    
    
endmodule