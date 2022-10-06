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

/* Import UVM macros and package */
`include "uvm_macros.svh"
import uvm_pkg::*;

`include "len5_config.svh"

import len5_pkg::*;
import expipe_pkg::*;
import memory_pkg::*;
import csr_pkg::*;

module tb_bare;
    // ----------------
    // TB CONFIGURATION
    // ----------------

    // Boot program counter
    localparam  FETCH_BOOT_PC   = `BOOT_PC;

    // Serial monitor and exit register address
    localparam  MON_MEM_ADDR    = `SERIAL_ADDR;
    localparam  EXIT_ADDR       = `EXIT_ADDR;

    // Memory emulator configuration
    localparam string MEM_DUMP_FILE = "mem_dump.txt";
    localparam  MEM_DUMP_T          = 0; // memory dump period (in cycles, 0 to disable)
    localparam  MEM_PIPE_NUM        = 0; // memory latency
    localparam  MEM_SKIP_INS_REG    = MEM_EMU_SKIP_INSTR_OUT_REG; // skip instruction output register
    localparam  MEM_SKIP_DATA_REG   = MEM_EMU_SKIP_DATA_OUT_REG;  // skip data output register

    // Datapath configuration
    // NOTE: the memory can accept a number of outstanding requests equal to
    // the number of its pipeline stages, plus the two internal registers of
    // the output spill cell, if implemented. The fetch stage must buffer the
    // same number of requests.
    localparam  FETCH_MEMIF_FIFO_DEPTH  = MEM_PIPE_NUM + ((MEM_SKIP_INS_REG) ? 0 : 2);

    // INTERNAL SIGNALS
    // ----------------

    // Input memory file (binary)
    string      mem_file = "memory.mem";

    // Number of cycles to simulate
    longint unsigned num_cycles = 0;    // 0: no boundary
    longint unsigned curr_cycle = 0;

    // Clock and reset
    logic       clk, rst_n;

    // Stop flag
    logic       tb_stop = 1'b0;

    // Serial monitor string
    string      serial_str;

    // Mmeory Emulator <--> Datapath
    logic       ins_mem_dp_valid;
    logic       ins_mem_dp_ready;
    logic       dp_ins_mem_valid;
    logic       dp_ins_mem_ready;
    mem_ans_t   ins_mem_dp_ans;
    mem_req_t   dp_ins_mem_req;
    logic       data_mem_dp_valid;
    logic       data_mem_dp_ready;
    logic       dp_data_mem_valid;
    logic       dp_data_mem_ready;
    mem_ans_t   data_mem_dp_ans;
    mem_req_t   dp_data_mem_req;

    // ----
    // BODY
    // ----

    // Command-line options and configuration
    // --------------------------------------
    initial begin
        // Set the memory file path
        if ($value$plusargs("MEM_FILE=%s", mem_file)) begin
            `uvm_info("CMDLINE", "Updated memory file", UVM_HIGH);
        end
        
        // Set the number of cycles to simulate
        if ($value$plusargs("N=%d", num_cycles)) begin
            `uvm_info("CMDLINE", "Updated number of simulation cycles", UVM_HIGH);
        end

        /* Print boot program counter */
        `uvm_info("CONFIG", $sformatf("Boot program counter: 0x%x", `BOOT_PC), UVM_INFO);

        /* Print the number of simulation cycles */
        `uvm_info("CONFIG", $sformatf("Number of simulation cycles: %0d", num_cycles), UVM_INFO);

        /* Print memory file being used */
        `uvm_info("CONFIG", $sformatf("Memory image: %s", mem_file), UVM_INFO);

        /* Print the serial monitor base address */
        `uvm_info("CONFIG", $sformatf("Serial monitor memory address: 0x%h", MON_MEM_ADDR), UVM_INFO);

        /* Print M extension information */
        `uvm_info("CONFIG", $sformatf("M extension: %s", `ifdef LEN5_M_EN "YES" `else "NO" `endif), UVM_INFO);
        
        /* Print FP extension information */
        `uvm_info("CONFIG", $sformatf("D extension: %s", `ifdef LEN5_FP_EN "YES" `else "NO" `endif), UVM_INFO);
    end

    // Clock and reset generation
    // --------------------------
    initial begin
        clk         = 1'b1;
        rst_n       = 1'b0;
        
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
                `uvm_info("TB", "Stopping simulation", UVM_INFO);
                `uvm_info("TB", "EXECUTION REPORT", UVM_INFO);
            `ifndef LEN5_CSR_HPMCOUNTERS_EN
                `uvm_info("TB", "NOTE: extra performance counters not available since 'LEN5_CSR_HPMCOUNTERS_EN' is not defined", UVM_MEDIUM);
            `endif /* LEN5_CSR_HPMCOUNTERS_EN */
                `uvm_info("TB", $sformatf("- current TB cycle:                      %0d", curr_cycle), UVM_INFO);
                `uvm_info("TB", $sformatf("- total CPU cycles:                      %0d", u_datapath.u_backend.u_csrs.mcycle), UVM_INFO);
                `uvm_info("TB", $sformatf("- retired instructions:                  %0d", u_datapath.u_backend.u_csrs.minstret), UVM_INFO);
            `ifdef LEN5_CSR_HPMCOUNTERS_EN
                `uvm_info("TB", $sformatf("  > retired branch/jump instructions:    %0d (%0.1f%%)", u_datapath.u_backend.u_csrs.hpmcounter3 + u_datapath.u_backend.u_csrs.hpmcounter4, real'(u_datapath.u_backend.u_csrs.hpmcounter3 + u_datapath.u_backend.u_csrs.hpmcounter4) * 100 / u_datapath.u_backend.u_csrs.minstret), UVM_INFO);
                `uvm_info("TB", $sformatf("    + jumps:                             %0d (%0.1f%%)", u_datapath.u_backend.u_csrs.hpmcounter3, real'(u_datapath.u_backend.u_csrs.hpmcounter3) * 100 / u_datapath.u_backend.u_csrs.minstret), UVM_INFO);
                `uvm_info("TB", $sformatf("    + branches:                          %0d (%0.1f%%)", u_datapath.u_backend.u_csrs.hpmcounter4, real'(u_datapath.u_backend.u_csrs.hpmcounter4) * 100 / u_datapath.u_backend.u_csrs.minstret), UVM_INFO);
                `uvm_info("TB", $sformatf("  > retired load/store instructions:     %0d (%0.1f%%)", u_datapath.u_backend.u_csrs.hpmcounter5 + u_datapath.u_backend.u_csrs.hpmcounter6, real'(u_datapath.u_backend.u_csrs.hpmcounter5 + u_datapath.u_backend.u_csrs.hpmcounter6) * 100 / u_datapath.u_backend.u_csrs.minstret), UVM_INFO);
                `uvm_info("TB", $sformatf("    + loads:                             %0d (%0.1f%%)", u_datapath.u_backend.u_csrs.hpmcounter5, real'(u_datapath.u_backend.u_csrs.hpmcounter5) * 100 / u_datapath.u_backend.u_csrs.minstret), UVM_INFO);
                `uvm_info("TB", $sformatf("    + stores:                            %0d (%0.1f%%)", u_datapath.u_backend.u_csrs.hpmcounter6, real'(u_datapath.u_backend.u_csrs.hpmcounter6) * 100 / u_datapath.u_backend.u_csrs.minstret), UVM_INFO);
            `endif /* LEN5_CSR_HPMCOUNTERS_EN */
                `uvm_info("TB", $sformatf("- average IPC:                           %0.2f", real'(u_datapath.u_backend.u_csrs.minstret) / curr_cycle), UVM_INFO);
                $stop;
            end
        join
    end
    always #5 clk   = ~clk;

    // Serial monitor
    // --------------
    always_ff @( posedge clk ) begin : serial_monitor
        byte c;

        // Sniff SERIAL ADDRESS and print content
        if (dp_data_mem_valid && dp_data_mem_req.addr == MON_MEM_ADDR && dp_data_mem_req.acc_type == MEM_ACC_ST) begin
            c = dp_data_mem_req.value[7:0];
            if (c == "\n") begin
                `uvm_info("TB SERIAL MONITOR", $sformatf("Detected newline:         [0x%h]", c), UVM_HIGH);
            end else if (c == "\0") begin
                `uvm_info("TB SERIAL MONITOR", $sformatf("Detected end of string:   [0x%h]", c), UVM_HIGH);
            end else begin
                `uvm_info("TB SERIAL MONITOR", $sformatf("Detected character:     %c [0x%h]", c, c), UVM_HIGH);
            end

            // Check for end-of-string
            if ((c == "\0" || c == "\n") && serial_str.len() > 0) begin
                `uvm_info("TB SERIAL MONITOR", $sformatf("Received string: \"%s\"", serial_str), UVM_LOW);
                serial_str = "";
            end else begin
                serial_str = {serial_str, c};
            end
        end
    end

    // Exit monitor
    // ------------
    // Stop the simulation after a certain memory location is written
    always_ff @( posedge clk ) begin : exit_monitor
        byte c;

        if (dp_data_mem_valid && dp_data_mem_req.addr == EXIT_ADDR && dp_data_mem_req.acc_type == MEM_ACC_ST) begin
            c = dp_data_mem_req.value[7:0];
            `uvm_info("TB EXIT MONITOR", $sformatf("Program exit with code: 0x%h", c), UVM_INFO);
            tb_stop <= 1'b1;
        end else tb_stop <= 0;
    end

    // -------
    // MODULES
    // -------

    // LEN5 BAREMETAL DATAPATH
    // -----------------------
    datapath #(
        .FETCH_MEMIF_FIFO_DEPTH (FETCH_MEMIF_FIFO_DEPTH ),
        .BOOT_PC                (FETCH_BOOT_PC)
    ) u_datapath (
    	.clk_i            (clk               ),
        .rst_n_i          (rst_n             ),
        .mem_flush_o      (dp_mem_flush      ),
        .ins_mem_valid_i  (ins_mem_dp_valid  ),
        .ins_mem_ready_i  (ins_mem_dp_ready  ),
        .ins_mem_valid_o  (dp_ins_mem_valid  ),
        .ins_mem_ready_o  (dp_ins_mem_ready  ),
        .ins_mem_ans_i    (ins_mem_dp_ans    ),
        .ins_mem_req_o    (dp_ins_mem_req    ),
        .data_mem_valid_i (data_mem_dp_valid ),
        .data_mem_ready_i (data_mem_dp_ready ),
        .data_mem_valid_o (dp_data_mem_valid ),
        .data_mem_ready_o (dp_data_mem_ready ),
        .data_mem_ans_i   (data_mem_dp_ans   ),
        .data_mem_req_o   (dp_data_mem_req   )
    );

    // MEMORY EMULATOR
    // ---------------
    memory_bare_emu #(
        .DUMP_PERIOD        (MEM_DUMP_T        ),
        .PIPE_NUM           (MEM_PIPE_NUM      ),
        .SKIP_INS_ANS_REG   (MEM_SKIP_INS_REG  ),
        .SKIP_DATA_ANS_REG  (MEM_SKIP_DATA_REG )
    ) u_memory_bare_emu (
    	.clk_i           (clk               ),
        .rst_n_i         (rst_n             ),
        .flush_i         (dp_mem_flush      ),
        .mem_file_i      (mem_file          ),
        .mem_dump_file_i (MEM_DUMP_FILE     ),
        .ins_valid_i     (dp_ins_mem_valid  ),
        .ins_ready_i     (dp_ins_mem_ready  ),
        .ins_valid_o     (ins_mem_dp_valid  ),
        .ins_ready_o     (ins_mem_dp_ready  ),
        .ins_req_i       (dp_ins_mem_req    ),
        .ins_ans_o       (ins_mem_dp_ans    ),
        .data_valid_i    (dp_data_mem_valid ),
        .data_ready_i    (dp_data_mem_ready ),
        .data_valid_o    (data_mem_dp_valid ),
        .data_ready_o    (data_mem_dp_ready ),
        .data_req_i      (dp_data_mem_req   ),
        .data_ans_o      (data_mem_dp_ans   )
    );

endmodule