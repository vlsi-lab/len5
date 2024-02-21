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

module tb_bare #(
  parameter string           MEM_DUMP_FILE = "mem_dump.txt",
  parameter longint unsigned BOOT_PC       = 64'h0,
  parameter longint unsigned SERIAL_ADDR   = 64'h20000000,
  parameter longint unsigned EXIT_ADDR     = 64'h20000100
) (
  input logic clk_i,  // simulation clock
  input logic rst_ni  // simulation reset
);

  import len5_pkg::*;
  import expipe_pkg::*;
  import memory_pkg::*;
  import csr_pkg::*;
  import len5_config_pkg::*;

  // ----------------
  // TB CONFIGURATION
  // ----------------
  // Memory emulator configuration
  localparam int unsigned MemDumpT = 0;  // memory dump period (in cycles, 0 to disable)
  localparam int unsigned MemPipeNum = 0;  // memory latency

  // Datapath configuration
  // NOTE: the memory can accept a number of outstanding requests equal to
  // the number of its pipeline stages, plus the two internal registers of
  // the output spill cell, if implemented. The fetch stage must buffer the
  // same number of requests.
  localparam bit MemEmuSkipInstrOutReg = 1'b0;
  localparam int unsigned FetchMemIfFifoDepth = MemPipeNum + ((MemEmuSkipInstrOutReg) ? 0 : 2);

  // INTERNAL SIGNALS
  // ----------------
  // Memory file path
  string                              mem_file = "firmware.hex";

  // Number of cycles to simulate
  longint unsigned                    num_cycles = 0;

  // Number of cycles to simulate
  longint unsigned                    curr_cycle = 0;

  // Serial monitor
  bit                                 serial_recv;
  byte                                serial_char;
  string                              serial_str;

  // Exit monitor
  bit                                 exit_code_recv;
  byte                                exit_code_q;

  // Mmeory monitor
  longint unsigned                    num_instr_loads = 0;
  longint unsigned                    num_data_loads = 0;
  longint unsigned                    num_data_stores = 0;

  // Mmeory Emulator <--> Datapath
  logic                               dp2mem_flush;
  logic                               dp2mem_instr_valid;
  logic                               mem2dp_instr_ready;
  logic                               dp2mem_instr_ready;
  logic                               mem2dp_instr_valid;
  logic            [        XLEN-1:0] dp2mem_instr_addr;
  logic            [        ILEN-1:0] mem2dp_instr_rdata;
  logic                               mem2dp_instr_except_raised;
  except_code_t                       mem2dp_instr_except_code;

  logic                               dp2mem_load_valid;
  logic                               mem2dp_load_ready;
  logic                               mem2dp_load_valid;
  logic                               dp2mem_load_ready;
  logic            [        XLEN-1:0] dp2mem_load_addr;
  logic            [             7:0] dp2mem_load_be;
  logic            [BUFF_IDX_LEN-1:0] dp2mem_load_tag;
  logic            [        XLEN-1:0] mem2dp_load_rdata;
  logic            [BUFF_IDX_LEN-1:0] mem2dp_load_tag;
  logic                               mem2dp_load_except_raised;
  except_code_t                       mem2dp_load_except_code;

  logic                               dp2mem_store_valid;
  logic                               mem2dp_store_ready;
  logic                               dp2mem_store_ready;
  logic                               mem2dp_store_valid;
  logic                               dp2mem_store_we;
  logic            [        XLEN-1:0] dp2mem_store_addr;
  logic            [BUFF_IDX_LEN-1:0] dp2mem_store_tag;
  logic            [             7:0] dp2mem_store_be;
  logic            [        XLEN-1:0] dp2mem_store_wdata;
  logic            [BUFF_IDX_LEN-1:0] mem2dp_store_tag;
  logic                               mem2dp_store_except_raised;
  except_code_t                       mem2dp_store_except_code;

  // ----
  // BODY
  // ----

  // Command-line options and configuration
  // --------------------------------------
  initial begin
    // Set the firmware file path
    $value$plusargs("firmware=%s", mem_file);

    // Set the number of cycles to simulate
    $value$plusargs("max_cycles=%d", num_cycles);

    // Print firmware file being used
    $display("[TB] Firmware: %s", mem_file);

    // Print the number of cycles to simulate
    $display("[TB] Number of cycles to simulate: %0d", num_cycles);

    // Print boot program counter
    $display("[TB] Boot program counter: 0x%x", BOOT_PC);

    // Print memory file being used
    $display("[TB] Memory image: %s", mem_file);

    // Print the serial monitor base address
    $display("[TB] Serial regiter memory address: 0x%h", SERIAL_ADDR);

    // Print the exit monitor base address
    $display("[TB] Exit register memory address: 0x%h", EXIT_ADDR);

    // Print M extension information
    $display("[TB] M extension: %s", (LEN5_M_EN && LEN5_D_EN) ? "YES" : "NO");

    // Print FP extension information
    $display("[TB] D extension: %s", (LEN5_FP_EN) ? "YES" : "NO");

    if (num_cycles <= 0) begin
      $fatal("Maximum simulation cycles is lower or equal to 0. Exiting...");
    end

  end

  // Watchdog
  // --------
  //logic clk = 1'b0;
  //always #5 clk = ~clk;
  always_ff @(posedge clk_i) begin
    curr_cycle <= curr_cycle + 1;
    if (curr_cycle >= num_cycles) begin
      $fatal("[%t] Simulation timeout. Exiting...", $time);
    end
  end


  // Memory monitor
  // --------------
  // Track the number of issued memory requests
  always_ff @(posedge clk_i) begin : mem_monitor
    if (dp2mem_load_valid && mem2dp_load_ready) begin
      num_data_loads <= num_data_loads + 1;
    end
    if (dp2mem_store_valid && mem2dp_store_ready) begin
      num_data_stores <= num_data_stores + 1;
    end
    if (dp2mem_instr_valid && mem2dp_instr_ready) begin
      num_instr_loads <= num_instr_loads + 1;
    end
  end

  // Serial monitor
  // --------------
  always_ff @(posedge clk_i) begin : serial_monitor
    // Sniff SERIAL ADDRESS and print content
    if (dp2mem_store_valid && mem2dp_store_ready && dp2mem_store_addr == SERIAL_ADDR) begin
      serial_recv <= 1'b1;
      serial_char <= dp2mem_store_wdata[7:0];
    end else begin
      serial_recv <= 1'b0;
    end

    if (serial_recv) begin
      if (serial_char == "\n" || serial_char == "\r") begin
        $display("[%8t] SERIAL MONITOR > detected newline:         [0x%h]", $time, serial_char);
      end else if (serial_char == 8'h0) begin
        $display("[%8t] SERIAL MONITOR > detected end of string:   [0x%h]", $time, serial_char);
      end else begin
        $display("[%8t] SERIAL MONITOR > detected character:     %c [0x%h]", $time, serial_char,
                 serial_char);
      end

      // Check for end-of-string
      if ((serial_char == 8'h0 || serial_char == "\n" || serial_char == "\r") && serial_str.len() > 0) begin
        $display("\033[1m[%8t] SERIAL MONITOR > received string:\033[0m \"%s\"", $time, serial_str);
        serial_str <= "";
      end else begin
        serial_str <= {serial_str, serial_char};
      end
    end
  end

  // Exit monitor
  // ------------
  // Stop the simulation after a certain memory location is written
  always_ff @(posedge clk_i) begin : exit_monitor
    if (dp2mem_store_valid && dp2mem_store_addr == EXIT_ADDR) begin
      exit_code_q    <= dp2mem_store_wdata[7:0];
      exit_code_recv <= 1'b1;
    end else begin
      exit_code_recv <= 1'b0;
    end

    if (exit_code_recv) begin
      if (exit_code_q == 0) begin
        $display("\n\033[1;32m[%8t] TB > Program exit with code: 0x%h (SUCCESS)\033[0m\n", $time,
                 exit_code_q);
      end else begin
        $display("\n\033[1;31m[%8t] TB > Program exit with code: 0x%h (FAILURE)\033[0m\n", $time,
                 exit_code_q);
      end
      printReport();
      $finish();
    end
  end

  // -------
  // MODULES
  // -------

  // LEN5 BAREMETAL DATAPATH
  // -----------------------
  datapath #(
    .FETCH_MEMIF_FIFO_DEPTH(FetchMemIfFifoDepth),
    .BOOT_PC               (BOOT_PC)
  ) u_datapath (
    .clk_i                     (clk_i),
    .rst_ni                    (rst_ni),
    .mem_flush_o               (dp2mem_flush),
    .instr_req_o               (dp2mem_instr_valid),
    .instr_gnt_i               (mem2dp_instr_ready),
    .instr_rvalid_i            (mem2dp_instr_valid),
    .instr_rready_o            (dp2mem_instr_ready),
    .instr_we_o                (),
    .instr_addr_o              (dp2mem_instr_addr),
    .instr_rdata_i             (mem2dp_instr_rdata),
    .instr_except_raised_i     (mem2dp_instr_except_raised),
    .instr_except_code_i       (mem2dp_instr_except_code),
    .data_load_req_o           (dp2mem_load_valid),
    .data_load_gnt_i           (mem2dp_load_ready),
    .data_load_rvalid_i        (mem2dp_load_valid),
    .data_load_rready_o        (dp2mem_load_ready),
    .data_load_we_o            (),
    .data_load_addr_o          (dp2mem_load_addr),
    .data_load_be_o            (dp2mem_load_be),
    .data_load_tag_o           (dp2mem_load_tag),
    .data_load_rdata_i         (mem2dp_load_rdata),
    .data_load_tag_i           (mem2dp_load_tag),
    .data_load_except_raised_i (mem2dp_load_except_raised),
    .data_load_except_code_i   (mem2dp_load_except_code),
    .data_store_req_o          (dp2mem_store_valid),
    .data_store_gnt_i          (mem2dp_store_ready),
    .data_store_rvalid_i       (mem2dp_store_valid),
    .data_store_rready_o       (dp2mem_store_ready),
    .data_store_we_o           (dp2mem_store_we),
    .data_store_addr_o         (dp2mem_store_addr),
    .data_store_tag_o          (dp2mem_store_tag),
    .data_store_be_o           (dp2mem_store_be),
    .data_store_wdata_o        (dp2mem_store_wdata),
    .data_store_tag_i          (mem2dp_store_tag),
    .data_store_except_raised_i(mem2dp_store_except_raised),
    .data_store_except_code_i  (mem2dp_store_except_code),
    .irq_i                     (),
    .irq_ack_o                 (),
    .irq_id_o                  (),
    .fetch_enable_i            (),
    .core_sleep_o              ()
  );

  // MEMORY EMULATOR
  // ---------------
  memory_bare_emu #(
    .DUMP_PERIOD      (MemDumpT),
    .PIPE_NUM         (MemPipeNum),
    .SKIP_INS_ANS_REG (MemEmuSkipInstrOutReg),
    .SKIP_DATA_ANS_REG(1'b1)
  ) u_memory_bare_emu (
    .clk_i                     (clk_i),
    .rst_ni                    (rst_ni),
    .instr_flush_i             (dp2mem_flush),
    .mem_file_i                (mem_file),
    .mem_dump_file_i           (MEM_DUMP_FILE),
    .instr_valid_i             (dp2mem_instr_valid),
    .instr_valid_o             (mem2dp_instr_valid),
    .instr_ready_o             (mem2dp_instr_ready),
    .instr_ready_i             (dp2mem_instr_ready),
    .instr_addr_i              (dp2mem_instr_addr),
    .instr_rdata_o             (mem2dp_instr_rdata),
    .instr_except_raised_o     (mem2dp_instr_except_raised),
    .instr_except_code_o       (mem2dp_instr_except_code),
    .data_load_valid_i         (dp2mem_load_valid),
    .data_load_ready_o         (mem2dp_load_ready),
    .data_load_valid_o         (mem2dp_load_valid),
    .data_load_ready_i         (dp2mem_load_ready),
    .data_load_addr_i          (dp2mem_load_addr),
    .data_load_be_i            (dp2mem_load_be),
    .data_load_tag_i           (dp2mem_load_tag),
    .data_load_rdata_o         (mem2dp_load_rdata),
    .data_load_tag_o           (mem2dp_load_tag),
    .data_load_except_raised_o (mem2dp_load_except_raised),
    .data_load_except_code_o   (mem2dp_load_except_code),
    .data_store_valid_i        (dp2mem_store_valid),
    .data_store_ready_o        (mem2dp_store_ready),
    .data_store_valid_o        (mem2dp_store_valid),
    .data_store_ready_i        (dp2mem_store_ready),
    .data_store_we_i           (dp2mem_store_we),
    .data_store_addr_i         (dp2mem_store_addr),
    .data_store_tag_i          (dp2mem_store_tag),
    .data_store_be_i           (dp2mem_store_be),
    .data_store_wdata_i        (dp2mem_store_wdata),
    .data_store_tag_o          (mem2dp_store_tag),
    .data_store_except_raised_o(mem2dp_store_except_raised),
    .data_store_except_code_o  (mem2dp_store_except_code)
  );

  // ---------
  // FUNCTIONS
  // ---------

  // Print simulation report
  function automatic void printReport();
    automatic
    longint unsigned
    num_mem_requests = num_instr_loads + num_data_loads + num_data_stores;

    $display("### EXECUTION REPORT");
    $display("    - current TB cycle:                    %6d", curr_cycle);
    $display("    - total CPU cycles:                    %6d", u_datapath.u_backend.u_csrs.mcycle);
    $display(" ## retired instructions:                  %6d",
             u_datapath.u_backend.u_csrs.minstret);
    $display(" ## average IPC:                           %6.2f",
             real'(u_datapath.u_backend.u_csrs.minstret) / u_datapath.u_backend.u_csrs.mcycle);
    if (!LEN5_CSR_HPMCOUNTERS_EN) begin
      $display(
          "  # NOTE: extra performance counters not available since 'LEN5_CSR_HPMCOUNTERS_EN' is not defined");
    end else begin
      $display(
          " ## retired branch/jump instructions:      %6d (%0.1f%%)",
          u_datapath.u_backend.u_csrs.hpmcounter3 + u_datapath.u_backend.u_csrs.hpmcounter4,
          real'(u_datapath.u_backend.u_csrs.hpmcounter3 + u_datapath.u_backend.u_csrs.hpmcounter4) * 100 / u_datapath.u_backend.u_csrs.minstret);
      $display(
          "  # jumps:                                 %6d (%0.1f%%)",
          u_datapath.u_backend.u_csrs.hpmcounter3,
          real'(u_datapath.u_backend.u_csrs.hpmcounter3) * 100 / (u_datapath.u_backend.u_csrs.hpmcounter3 + u_datapath.u_backend.u_csrs.hpmcounter4));
      $display(
          "  # branches:                              %6d (%0.1f%%)",
          u_datapath.u_backend.u_csrs.hpmcounter4,
          real'(u_datapath.u_backend.u_csrs.hpmcounter4) * 100 / (u_datapath.u_backend.u_csrs.hpmcounter3 + u_datapath.u_backend.u_csrs.hpmcounter4));
      $display(
          " ## retired load/store instructions:       %6d (%0.1f%%)",
          u_datapath.u_backend.u_csrs.hpmcounter5 + u_datapath.u_backend.u_csrs.hpmcounter6,
          real'(u_datapath.u_backend.u_csrs.hpmcounter5 + u_datapath.u_backend.u_csrs.hpmcounter6) * 100 / u_datapath.u_backend.u_csrs.minstret);
      $display(
          "  # loads:                                 %6d (%0.1f%%)",
          u_datapath.u_backend.u_csrs.hpmcounter5,
          real'(u_datapath.u_backend.u_csrs.hpmcounter5) * 100 / (u_datapath.u_backend.u_csrs.hpmcounter5 + u_datapath.u_backend.u_csrs.hpmcounter6));
      $display(
          "  # stores:                                %6d (%0.1f%%)",
          u_datapath.u_backend.u_csrs.hpmcounter6,
          real'(u_datapath.u_backend.u_csrs.hpmcounter6) * 100 / (u_datapath.u_backend.u_csrs.hpmcounter5 + u_datapath.u_backend.u_csrs.hpmcounter6));
    end
    $display(" ## memory requests:                       %6d",
             num_data_loads + num_data_stores + num_instr_loads);
    $display("  # load instr. memory requests:           %6d (%0.2f%%)", num_instr_loads,
             real'(num_instr_loads) * 100 / num_mem_requests);
    $display("  # load data memory requests:             %6d (%0.2f%%)", num_data_loads,
             real'(num_data_loads) * 100 / num_mem_requests);
    $display("  # store data memory requests:            %6d (%0.2f%%)", num_data_stores,
             real'(num_data_stores) * 100 / num_mem_requests);
  endfunction : printReport

endmodule
