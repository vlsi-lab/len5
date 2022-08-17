// Copyright 2022 Politecnico di Torino.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// File: tb_bare.sv
// Author: Michele Caon
// Date: 17/08/2022

// LEN5 compilation switches
`include "len5_config.svh"

/* Import UVM macros and package */
`include "uvm_macros.svh"
import uvm_pkg::*;

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module tb_bare;
    // ----------------
    // TB CONFIGURATION
    // ----------------

    // Initial program counter
    localparam logic [XLEN-1:0] BOOT_PC = `BOOT_PC;
    localparam                  BPU_HISTORY_LEN = 4;
    localparam                  BPU_BTB_BITS    = 4;

    // Memory dump period (in clock cycles)
    localparam          MEM_DUMP_T = 20;

    // Memory file
    localparam string   MEM_DUMP_FILE = "mem_dump.txt";

    // INTERNAL SIGNALS
    // ----------------

    // Input memory file
    string      mem_file = "memory.txt";

    // Number of cycles to simulate
    longint unsigned num_cycles = 0;    // 0: no boundary

    // Clock and reset
    logic clk, rst_n;

    // Mmeory Emulator <--> Datapath
    logic       dp_mem_valid;
    logic       dp_mem_ready;
    logic       mem_dp_valid;
    logic       mem_dp_ready;
    mem_req_t   dp_mem_req;
    mem_ans_t   mem_dp_ans;

    // ----
    // BODY
    // ----

    // Command-line options and configuration
    // --------------------------------------
    initial begin
        // Set the memory file path
        if ($value$plusargs("MEM_FILE=%s", mem_file)) begin
            `uvm_info("CMDLINE", "Updated memory file", UVM_INFO);
        end
        
        // Set the number of cycles to simulate
        if ($value$plusargs("N=%d", num_cycles)) begin
            `uvm_info("CMDLINE", "Updated number of simulation cycles", UVM_INFO);
        end

        /* Print boot program counter */
        `uvm_info("CONFIG", $sformatf("Boot program counter: 0x%x", BOOT_PC), UVM_MEDIUM);

        /* Print the number of simulation cycles */
        `uvm_info("CONFIG", $sformatf("Number of simulation cycles: %0d", num_cycles), UVM_MEDIUM);

        /* Print memory file being used */
        `uvm_info("CONFIG", $sformatf("Memory file: %s", mem_file), UVM_MEDIUM);

        /* Print M extension information */
        `uvm_info("CONFIG", $sformatf("M extension: %s", `ifdef LEN5_M_EN "YES" `else "NO" `endif), UVM_MEDIUM);
        
        /* Print FP extension information */
        `uvm_info("CONFIG", $sformatf("D extension: %s", `ifdef LEN5_FP_EN "YES" `else "NO" `endif), UVM_MEDIUM);
    end

    // Clock and reset generation
    // --------------------------
    initial begin
        clk         = 1;
        rst_n       = 0;
        
        #10 rst_n = 1;
    end
    always #5 clk   = ~clk;

    // -------
    // MODULES
    // -------

    // LEN5 BAREMETAL DATAPATH
    // -----------------------
    datapath #(
        .PC_GEN_BOOT_PC  (BOOT_PC  ),
        .BPU_HISTORY_LEN (BPU_HISTORY_LEN ),
        .BPU_BTB_BITS    (BPU_BTB_BITS    )
    ) u_datapath (
    	.clk_i       (clk          ),
        .rst_n_i     (rst_n        ),
        .mem_valid_i (mem_dp_valid ),
        .mem_ready_i (mem_dp_ready ),
        .mem_valid_o (dp_mem_valid ),
        .mem_ready_o (dp_mem_ready ),
        .mem_ans_i   (mem_dp_ans   ),
        .mem_req_o   (dp_mem_req   )
    );

    // MEMORY EMULATOR
    // ---------------
    memory_bare_emu #(
        .DUMP_PERIOD (MEM_DUMP_T )
    ) u_memory_bare_emu (
    	.clk_i           (clk_i           ),
        .rst_n_i         (rst_n_i         ),
        .flush_i         (flush_i         ),
        .mem_file_i      (mem_file        ),
        .mem_dump_file_i (MEM_DUMP_FILE   ),
        .valid_i         (dp_mem_valid    ),
        .ready_i         (dp_mem_ready    ),
        .valid_o         (mem_dp_valid    ),
        .ready_o         (mem_dp_ready    ),
        .req_i           (dp_mem_req      ),
        .ans_o           (mem_dp_ans      )
    );

endmodule