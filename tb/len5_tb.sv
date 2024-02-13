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
// File: len5_tb.sv
// Author: Michele Caon
// Date: 30/01/2024

module len5_tb;
  // ----------------
  // TB CONFIGURATION
  // ----------------
  // Reset duration
  localparam int unsigned ResetCycles = 10;

  // Boot program counter
  localparam longint unsigned BootPC = 64'h180;
  localparam string MemDumpFile = "mem_dump.txt";

  // INTERNAL SIGNALS
  // ----------------
  // Memory file path
  string           mem_file = "firmware.hex";

  // Number of cycles to simulate
  longint unsigned num_cycles = 0;

  // Clock and reset
  logic clk, rst_n;

  // ----
  // BODY
  // ----

  // Command-line options and configuration
  // --------------------------------------
  initial begin
    // Set the firmware file path
    if ($value$plusargs("firmware=%s", mem_file)) begin
      $display("Updated firmware");
    end

    // Set the number of cycles to simulate
    if ($value$plusargs("N=%d", num_cycles)) begin
      $display("Updated number of simulation cycles");
    end
  end

  // Clock and reset generation
  // --------------------------
  initial begin
    clk   = 1'b1;
    rst_n = 1'b0;

    // De-assert reset after some cycles
    repeat (ResetCycles) @(posedge clk);
    rst_n = 1'b1;
  end
  always #5 clk = ~clk;

  // --------------
  // LEN5 TB SYSTEM
  // --------------
  tb_bare #(
    .MEM_DUMP_FILE(MemDumpFile),
    .BOOT_PC      (BootPC)
  ) u_tb (
    .clk_i       (clk),        // simulation clock
    .rst_ni      (rst_n),      // simulation reset
    .mem_file_i  (mem_file),   // memory file, in ASCII HEX format
    .num_cycles_i(num_cycles)  // number of cycles to simulate
  );
endmodule
