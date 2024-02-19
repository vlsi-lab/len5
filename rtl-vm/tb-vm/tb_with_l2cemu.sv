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

import len5_config_pkg::*;
import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module tb_with_l2cemu;

  // ----------------
  // TB CONFIGURATION
  // ----------------

  // Memory dump period (in clock cycles)
  localparam int unsigned MemDumpT = 20;

  // Memory file
  localparam string MemDumpFile = "mem_dump.txt";

  // INTERNAL SIGNALS
  // ----------------

  // Input memory file
  string           mem_file = "memory.txt";

  // Number of cycles to simulate
  longint unsigned num_cycles = 0;  // 0: no boundary

  // Clock and reset
  logic            clk;
  logic            rst_n;

  // L2 Cache Arbiter <--> L2 Cache Emulator
  l2arb_l2c_req_t  l2arb_l2c_req;
  logic            l2c_l2arb_req_rdy;
  l2c_l2arb_ans_t  l2c_l2arb_ans;
  logic            l2arb_l2c_ans_rdy;
  logic            dp_l2c_flush;

  // ----
  // BODY
  // ----

  // Command-line options and configuration
  // --------------------------------------
  initial begin
    // Set the memory file path
    if ($value$plusargs("MEM_FILE=%s", mem_file)) begin
      $display("Updated memory file");
    end

    // Set the number of cycles to simulate
    if ($value$plusargs("N=%d", num_cycles)) begin
      $display("Updated number of simulation cycles");
    end

    /* Print boot program counter */
    $display("Boot program counter: 0x%x", BOOT_PC);

    /* Print the number of simulation cycles */
    $display("Number of simulation cycles: %0d", num_cycles);

    /* Print memory file being used */
    $display("Memory file: %s", mem_file);

    /* Print M extension information */
    $display("M extension: %s",
                       `ifdef LEN5_M_EN "YES"
                       `else
                       "NO"
                       `endif
                       );

    /* Print FP extension information */
    $display("D extension: %s",
                       `ifdef LEN5_FP_EN "YES"
                       `else
                       "NO"
                       `endif
                       );
  end

  // Clock and reset generation
  // --------------------------

  initial begin
    clk   = 1;
    rst_n = 0;

    #10 rst_n = 1;

    // Periodically dump memory content
    forever begin
      repeat (MemDumpT) @(posedge clk);
      if (0 != u_cache_L2_system_emulator.i_memory.PrintMem(MemDumpFile)) begin
        $display("ERROR while dumping memory content");
      end
    end
  end
  always #5 clk = ~clk;

  // Load memory
  // -----------
  int ret = 0;
  initial begin
    @(negedge clk);
    $display("Flashing memory from '%s'...", mem_file);
    ret = u_cache_L2_system_emulator.i_memory.LoadMem(mem_file);
    if (0 > ret) begin
      $display("ERROR while flashing memory");
    end
    $display(" - loaded %0d words", ret);

    // Stop the simulation after the requested number of cycles
    if (num_cycles > 0) begin
      repeat (num_cycles) @(posedge clk);
      $stop();
    end
  end

  // ---
  // DUT
  // ---

  // LEN5 Datapath
  // --------------

  datapath u_datapath (
    .clk_i              (clk),
    .rst_ni            (rst_n),
    .l2c_l2arb_req_rdy_i(l2c_l2arb_req_rdy),
    .l2c_l2arb_ans_i    (l2c_l2arb_ans),
    .l2arb_l2c_req_o    (l2arb_l2c_req),
    .l2arb_l2c_ans_rdy_o(l2arb_l2c_ans_rdy),
    .l2c_flush_o        (dp_l2c_flush)
  );

  // ------------
  // L2$ EMULATOR
  // ------------

  cache_L2_system_emulator u_cache_L2_system_emulator (
    .clk_i              (clk),
    .rst_ni             (rst_n),
    .flush_i            (dp_l2c_flush),
    .l2arb_l2c_req_i    (l2arb_l2c_req),
    .l2c_l2arb_req_rdy_o(l2c_l2arb_req_rdy),
    .l2c_l2arb_ans_o    (l2c_l2arb_ans),
    .l2arb_l2c_ans_rdy_i(l2arb_l2c_ans_rdy),

    .mem_file_i(mem_file)
  );

endmodule
