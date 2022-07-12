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
// File: tb_with_l2cemu.sv
// Author: Michele Caon
// Date: 23/11/2021

// LEN5 compilation switches
`include "len5_config.svh"

/* Import UVM macros and package */
`include "uvm_macros.svh"
import uvm_pkg::*;

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module tb_with_l2cemu;

    // ----------------
    // TB CONFIGURATION
    // ----------------

    // Initial program counter
    localparam logic [XLEN-1:0] BOOT_PC = `BOOT_PC;

    // Memory dump period (in clock cycles)
    localparam MEM_DUMP_T = 20;

    // Memory file
    localparam string MEM_DUMP_FILE = "mem_dump.txt";

    // INTERNAL SIGNALS
    // ----------------

    // Input memory file
    string      mem_file = "memory.txt";

    // Number of cycles to simulate
    longint unsigned num_cycles = 0;    // 0: no boundary

    // Clock and reset
    logic clk;
	logic rst_n;
	
  	// L2 Cache Arbiter <--> L2 Cache Emulator
	l2arb_l2c_req_t         l2arb_l2c_req;
  	logic                   l2c_l2arb_req_rdy;
  	l2c_l2arb_ans_t         l2c_l2arb_ans;
  	logic                   l2arb_l2c_ans_rdy;
    logic                   dp_l2c_flush;

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

        // Periodically dump memory content
        forever begin
            repeat (MEM_DUMP_T) @(posedge clk);
            if (0 != u_cache_L2_system_emulator.i_memory.PrintMem(MEM_DUMP_FILE)) begin
                `uvm_fatal("TB", "ERROR while dumping memory content");
            end
        end
    end
    always #5 clk   = ~clk;

    // Load memory
    // -----------
    int ret = 0;
    initial begin
        @(negedge clk);
        `uvm_info("FLASH", $sformatf("Flashing memory from '%s'...", mem_file), UVM_INFO);
        ret = u_cache_L2_system_emulator.i_memory.LoadMem(mem_file);
        if (0 > ret) begin
            `uvm_fatal("TB", "ERROR while flashing memory");
        end
        `uvm_info("FLASH", $sformatf(" - loaded %0d words", ret), UVM_INFO);

        // Stop the simulation after the requested number of cycles
        if (num_cycles > 0) begin
            repeat (num_cycles) @(posedge clk);
            $stop;
        end
    end
    
    // ---
    // DUT
    // ---

    // LEN5 Datapath
    // --------------

    datapath u_datapath
    (
        .clk_i                  (clk),
        .rst_n_i                (rst_n),
        .l2c_l2arb_req_rdy_i    (l2c_l2arb_req_rdy),
        .l2c_l2arb_ans_i        (l2c_l2arb_ans),
        .l2arb_l2c_req_o        (l2arb_l2c_req),
        .l2arb_l2c_ans_rdy_o    (l2arb_l2c_ans_rdy),
        .l2c_flush_o            (dp_l2c_flush)
    );

    // ------------
    // L2$ EMULATOR
    // ------------

    cache_L2_system_emulator u_cache_L2_system_emulator
    (
        .clk_i                  (clk),
        .rst_ni                 (rst_n),
        .flush_i                (dp_l2c_flush),
        .l2arb_l2c_req_i        (l2arb_l2c_req),
        .l2c_l2arb_req_rdy_o    (l2c_l2arb_req_rdy),
        .l2c_l2arb_ans_o        (l2c_l2arb_ans),
        .l2arb_l2c_ans_rdy_i    (l2arb_l2c_ans_rdy),

        .mem_file_i             (mem_file)
    );
    
endmodule