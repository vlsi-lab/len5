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

import len5_config_pkg::*;
import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module tb_bare;
  // ----------------
  // TB CONFIGURATION
  // ----------------

  // Boot program counter
  localparam int unsigned FetchBootPC = BOOT_PC;

  // Memory emulator configuration
  localparam string MemDumpFile = "mem_dump.txt";
  localparam int unsigned MemDumpT = 0;  // memory dump period (in cycles, 0 to disable)
  localparam int unsigned MemPipeNum = 0;  // memory latency

  // Datapath configuration
  // NOTE: the memory can accept a number of outstanding requests equal to
  // the number of its pipeline stages, plus the two internal registers of
  // the output spill cell, if implemented. The fetch stage must buffer the
  // same number of requests.
  localparam int unsigned FetchMemIfFifoDepth = MemPipeNum + ((MEM_EMU_SKIP_INSTR_OUT_REG) ? 0 : 2);

  // INTERNAL SIGNALS
  // ----------------

  // Input memory file (binary)
  string           mem_file = "memory.mem";

  // Number of cycles to simulate
  longint unsigned num_cycles = 0;  // 0: no boundary
  longint unsigned curr_cycle = 0;

  // Clock and reset
  logic clk, rst_n;

  // Stop flag
  logic            tb_stop = 1'b0;

  // Serial monitor string
  string           serial_str;

  // Mmeory monitor
  longint unsigned num_instr_loads = 0;
  longint unsigned num_data_loads = 0;
  longint unsigned num_data_stores = 0;

  // Mmeory Emulator <--> Datapath
  logic            ins_mem_dp_valid;
  logic            ins_mem_dp_ready;
  logic            dp_ins_mem_valid;
  logic            dp_ins_mem_ready;
  mem_ans_t        ins_mem_dp_ans;
  mem_req_t        dp_ins_mem_req;
  logic            data_mem_dp_valid;
  logic            data_mem_dp_ready;
  logic            dp_data_mem_valid;
  logic            dp_data_mem_ready;
  mem_ans_t        data_mem_dp_ans;
  mem_req_t        dp_data_mem_req;

  // ----
  // BODY
  // ----

  // Command-line options and configuration
  // --------------------------------------
  initial begin
    // Set the memory file path
    if ($value$plusargs("=%s", mem_file)) begin
      $display("Updated memory file");
    end

    // Set the number of cycles to simulate
    if ($value$plusargs("N=%d", num_cycles)) begin
      $display("Updated number of simulation cycles");
    end

    /* Print boot program counter */
    $display($sformatf("Boot program counter: 0x%x", BOOT_PC));

    /* Print the number of simulation cycles */
    $display($sformatf("Number of simulation cycles: %0d", num_cycles));

    /* Print memory file being used */
    $display($sformatf("Memory image: %s", mem_file));

    /* Print the serial monitor base address */
    $display($sformatf("Serial monitor memory address: 0x%h", SERIAL_ADDR));

    /* Print M extension information */
    $display($sformatf("M extension: %s",
                       `ifdef LEN5_M_EN "YES"
                       `else
                       "NO"
                       `endif
                       ));

    /* Print FP extension information */
    $display($sformatf("D extension: %s",
                       `ifdef LEN5_FP_EN "YES"
                       `else
                       "NO"
                       `endif
                       ));
  end

  // Clock and reset generation
  // --------------------------
  initial begin
    clk   = 1'b1;
    rst_n = 1'b0;

    #10 rst_n = 1'b1;

    fork
      begin
        if (num_cycles > 0) begin
          repeat (num_cycles) begin
            @(posedge clk);
            curr_cycle += 1;
          end
          $stop;
        end
      end

      begin
        @(posedge tb_stop);
        repeat (10) @(posedge clk);
        $display("Stopping simulation");
        printReport();
        $stop;
      end
    join
  end
  always #5 clk = ~clk;

  // Memory monitor
  // --------------
  // Track the number of issued memory requests
  always_ff @(posedge clk) begin : mem_monitor
    if (dp_data_mem_valid && data_mem_dp_ready) begin
      case (dp_data_mem_req.acc_type)
        MEM_ACC_LD: num_data_loads++;
        MEM_ACC_ST: num_data_stores++;
        default: begin
          $fatal($sformatf("Detected invalid data memory request at 0x%h", dp_data_mem_req.addr));
        end
      endcase
    end
    if (dp_ins_mem_valid && ins_mem_dp_ready) begin
      if (dp_ins_mem_req.acc_type == MEM_ACC_INSTR) begin
        num_instr_loads++;
      end else begin
        fatal($sformatf("Detected invalid instruction memory request at 0x%h", dp_data_mem_req.addr
              ));
      end
    end
  end

  // Serial monitor
  // --------------
  always_ff @(posedge clk) begin : serial_monitor
    byte c;

    // Sniff SERIAL ADDRESS and print content
    if (dp_data_mem_valid && dp_data_mem_req.addr == SERIAL_ADDR && dp_data_mem_req.acc_type == MEM_ACC_ST) begin
      c <= dp_data_mem_req.value[7:0];
      if (c == "\n") begin
        $display($sformatf("Detected newline:         [0x%h]", c));
      end else if (c == "\0") begin
        $display($sformatf("Detected end of string:   [0x%h]", c));
      end else begin
        $display($sformatf("Detected character:     %c [0x%h]", c, c),);
      end

      // Check for end-of-string
      if ((c == "\0" || c == "\n") && serial_str.len() > 0) begin
        $display($sformatf("Received string: \"%s\"", serial_str));
        serial_str <= "";
      end else begin
        serial_str <= {serial_str, c};
      end
    end
  end

  // Exit monitor
  // ------------
  // Stop the simulation after a certain memory location is written
  always_ff @(posedge clk) begin : exit_monitor
    byte c;

    if (dp_data_mem_valid && dp_data_mem_req.addr == EXIT_ADDR && dp_data_mem_req.acc_type == MEM_ACC_ST) begin
      c <= dp_data_mem_req.value[7:0];
      $display($sformatf("Program exit with code: 0x%h", c));
      tb_stop <= 1'b1;
    end else tb_stop <= 0;
  end

  // -------
  // MODULES
  // -------

  // LEN5 BAREMETAL DATAPATH
  // -----------------------
  datapath #(
    .FetchMemIfFifoDepth(FetchMemIfFifoDepth),
    .BOOT_PC            (FetchBootPC)
  ) u_datapath (
    .clk_i           (clk),
    .rst_n_i         (rst_n),
    .mem_flush_o     (dp_mem_flush),
    .ins_mem_valid_i (ins_mem_dp_valid),
    .ins_mem_ready_i (ins_mem_dp_ready),
    .ins_mem_valid_o (dp_ins_mem_valid),
    .ins_mem_ready_o (dp_ins_mem_ready),
    .ins_mem_ans_i   (ins_mem_dp_ans),
    .ins_mem_req_o   (dp_ins_mem_req),
    .data_mem_valid_i(data_mem_dp_valid),
    .data_mem_ready_i(data_mem_dp_ready),
    .data_mem_valid_o(dp_data_mem_valid),
    .data_mem_ready_o(dp_data_mem_ready),
    .data_mem_ans_i  (data_mem_dp_ans),
    .data_mem_req_o  (dp_data_mem_req)
  );

  // MEMORY EMULATOR
  // ---------------
  memory_bare_emu #(
    .DUMP_PERIOD      (MemDumpT),
    .PIPE_NUM         (MemPipeNum),
    .SKIP_INS_ANS_REG (MEM_EMU_SKIP_INSTR_OUT_REG),
    .SKIP_DATA_ANS_REG(MEM_EMU_SKIP_DATA_OUT_REG)
  ) u_memory_bare_emu (
    .clk_i          (clk),
    .rst_n_i        (rst_n),
    .flush_i        (dp_mem_flush),
    .mem_file_i     (mem_file),
    .mem_dump_file_i(MemDumpFile),
    .ins_valid_i    (dp_ins_mem_valid),
    .ins_ready_i    (dp_ins_mem_ready),
    .ins_valid_o    (ins_mem_dp_valid),
    .ins_ready_o    (ins_mem_dp_ready),
    .ins_req_i      (dp_ins_mem_req),
    .ins_ans_o      (ins_mem_dp_ans),
    .data_valid_i   (dp_data_mem_valid),
    .data_ready_i   (dp_data_mem_ready),
    .data_valid_o   (data_mem_dp_valid),
    .data_ready_o   (data_mem_dp_ready),
    .data_req_i     (dp_data_mem_req),
    .data_ans_o     (data_mem_dp_ans)
  );

  // ---------
  // FUNCTIONS
  // ---------

  // Print simulation report
  function automatic void printReport();
    automatic
    longint unsigned
    num_mem_requests = num_instr_loads + num_data_loads + num_data_stores;

    $display("EXECUTION REPORT");
`ifndef LEN5_CSR_HPMCOUNTERS_EN
    $display(
        "NOTE: extra performance counters not available since 'LEN5_CSR_HPMCOUNTERS_EN' is not defined",);
`endif  /* LEN5_CSR_HPMCOUNTERS_EN */
    $display($sformatf("- current TB cycle:                      %0d", curr_cycle),);
    $display($sformatf("- total CPU cycles:                      %0d",
                       u_datapath.u_backend.u_csrs.mcycle));
    $display($sformatf("- retired instructions:                  %0d",
                       u_datapath.u_backend.u_csrs.minstret));
`ifdef LEN5_CSR_HPMCOUNTERS_EN
    $display(
        $sformatf(
            "  > retired branch/jump instructions:    %0d (%0.1f%%)",
            u_datapath.u_backend.u_csrs.hpmcounter3 + u_datapath.u_backend.u_csrs.hpmcounter4,
            real'(u_datapath.u_backend.u_csrs.hpmcounter3 + u_datapath.u_backend.u_csrs.hpmcounter4) * 100 / u_datapath.u_backend.u_csrs.minstret),);
    $display(
        $sformatf(
            "    + jumps:                             %0d (%0.1f%%)",
            u_datapath.u_backend.u_csrs.hpmcounter3,
            real'(u_datapath.u_backend.u_csrs.hpmcounter3) * 100 / u_datapath.u_backend.u_csrs.minstret),);
    $display(
        $sformatf(
            "    + branches:                          %0d (%0.1f%%)",
            u_datapath.u_backend.u_csrs.hpmcounter4,
            real'(u_datapath.u_backend.u_csrs.hpmcounter4) * 100 / u_datapath.u_backend.u_csrs.minstret),);
    $display(
        $sformatf(
            "  > retired load/store instructions:     %0d (%0.1f%%)",
            u_datapath.u_backend.u_csrs.hpmcounter5 + u_datapath.u_backend.u_csrs.hpmcounter6,
            real'(u_datapath.u_backend.u_csrs.hpmcounter5 + u_datapath.u_backend.u_csrs.hpmcounter6) * 100 / u_datapath.u_backend.u_csrs.minstret),);
    $display(
        $sformatf(
            "    + loads:                             %0d (%0.1f%%)",
            u_datapath.u_backend.u_csrs.hpmcounter5,
            real'(u_datapath.u_backend.u_csrs.hpmcounter5) * 100 / u_datapath.u_backend.u_csrs.minstret),);
    $display(
        $sformatf(
            "    + stores:                            %0d (%0.1f%%)",
            u_datapath.u_backend.u_csrs.hpmcounter6,
            real'(u_datapath.u_backend.u_csrs.hpmcounter6) * 100 / u_datapath.u_backend.u_csrs.minstret),);
`endif  /* LEN5_CSR_HPMCOUNTERS_EN */
    $display($sformatf("- average IPC:                           %0.2f",
                       real'(u_datapath.u_backend.u_csrs.minstret) / curr_cycle));
    $display($sformatf("- memory requests:                       %0d",
                       num_data_loads + num_data_stores + num_instr_loads));
    $display($sformatf("  > load instr. memory requests:         %0d (%0.2f%%)", num_instr_loads,
                       real'(num_instr_loads) * 100 / num_mem_requests));
    $display($sformatf("  > load data memory requests :          %0d (%0.2f%%)", num_data_loads,
                       real'(num_data_loads) * 100 / num_mem_requests));
    $display($sformatf("  > store data memory requests :         %0d (%0.2f%%)", num_data_stores,
                       real'(num_data_stores) * 100 / num_mem_requests));
  endfunction : printReport

endmodule
