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
// File: len5_config_pkg.sv
// Author: Michele Caon
// Date: 04/11/2021

package len5_config_pkg;
  // --------------------
  // GLOBAL CONFIGURATION
  // --------------------
  // Boot memory translation mode
  typedef enum logic [1:0] {
    BARE,
    SV39,
    SV48
  } boot_mode_t;
  localparam boot_mode_t BOOT_VM_MODE = BARE;  // BARE|SV39|SV48

  // Boot program counter
  localparam logic [63:0] BOOT_PC = 64'h180;

  // MEMORY-MAPPED DEVICES
  // ---------------------
  // Address mask for memory-mapped devices
  // This mask defines the address range that is reserved to memory-mapped
  // devices. Store-to-load forwarding (see below) in this region is not
  // performed. This must be consistent with PERI_BASE in `len5.h`.
  localparam logic [63:0] MMAP_MASK = 64'hffffffffe0000000;  // above 512MB

  // FRONTEND PARAMETERS
  // -------------------
  // BPU g-share predictor global history length
  localparam int unsigned BPU_HLEN = 4;
  // BPU Branch Target Buffer (BTB) addressing bits (the remaining ones are used
  // as tag)
  localparam int unsigned BPU_BTB_BITS = 4;

  // -------------------
  // PIPELINE PARAMETERS
  // -------------------
  // The following switches enable or disable some of the sequential elements
  // inside some functional units, therefore reducing the latency at the
  // expense of increased delay on the involved lines. The increased delay
  // may impact on the operation frequency if the combinational unit enters
  // the processor critical path. The pipeline of the processor can handle
  // functional units with arbitrary latency, including 0-cycle, so this
  // changes do not require any modification.

  // FETCH STAGE
  // -----------
  // Fetch memory interface
  // NOTE: if the memory is 0-latency, at least one of the fetch unit registers
  // must be enabled (i.e., not skipped). Therefore, at least one of the
  // following switches must be commented in this case.
  localparam bit FETCH_REQ_SPILL_SKIP = 1'b1; // memory requests from the fetch unit are directly passed to the memory
  localparam bit FETCH_ANS_SPILL_SKIP = 1'b0; // fetched instructions are directly passed to the issue stage

  // EXECUTION PIPELINE
  // ------------------
  // ISSUE QUEUE
  localparam int unsigned IQ_DEPTH = 2;  // number of entries in the issue queue (power of 2)

  // LOAD/STORE UNIT
  localparam int unsigned LDBUFF_DEPTH = 4;  // number of entries in the load buffer
  localparam int unsigned STBUFF_DEPTH = 8;  // number of entries in the store buffer
  localparam bit LSU_SPILL_SKIP = 1'b1;  // make address adder fully combinational

  // ALU UNIT
  localparam int unsigned ALU_RS_DEPTH = 4;
  localparam bit ALU_SPILL_SKIP = 1'b1;  // make the ALU fully combinational

  // MULT/DIV UNIT
  localparam int unsigned MULT_RS_DEPTH = 4;
  localparam int unsigned DIV_RS_DEPTH = 4;
  localparam int unsigned DIV_PIPE_DEPTH = 8;

  // BRANCH UNIT
  localparam int unsigned BU_RS_DEPTH = 4;
  localparam bit BU_SPILL_SKIP = 1'b1;  // make the target address adder fully combinational

  // COMMIT STAGE
  localparam int unsigned ROB_DEPTH  /* verilator public */ = 16;  // Number of entries in the ROB
  localparam bit COMMIT_SPILL_SKIP = 1'b1;  // directly connect the commit CU to the ROB output

  // -----------------
  // FEATURES SWITCHES
  // -----------------

  // Enable store-to-load forwarding
  // -------------------------------
  // This switch instantiates a small cache with the same size as store buffer
  // inside the Load-Store Unit. This cache records the store buffer entry
  // containing the latest instruction that wrote a certain memory location.
  // When a load instruction accesses the same location, the forwarding of the
  // stored result is attempted.
  // IMPORTANT: this feature breaks reads from memory-mapped devices, therefore
  // it is only applied to memory addresses outside of the region masked by
  // 'MMAP_MASK' (defined above).
  localparam bit LEN5_STORE_LOAD_FWD_EN = 1'b1;

  // Enable C extension
  // ------------------
  // NOTE: CURRENTLY UNSUPPORTED
  localparam bit LEN5_C_EN = 1'b0;

  // Enable M extension support
  // --------------------------
  localparam bit LEN5_M_EN = 1'b1;
  localparam bit LEN5_MULT_SERIAL = 1'b0;
  localparam bit LEN5_DIV_EN = 1'b1;  // TODO: div available

  // Enable floating-point support
  // -----------------------------
  localparam bit LEN5_FP_EN = 1'b0;

  // Enable atomic support
  // ---------------------
  localparam bit LEN5_A_EN = 1'b0;

  // Maximum number of execution units :
  // load buffer, store buffer, branch unit, ALU, MULT, DIV
  localparam int unsigned MAX_EU_N = 6;

  // Reservation stations
  // --------------------
  // If defined, the arbiters of the shared virtual address adder, the DTLB and the DCACHE will give the highest priority to the store buffer in case of conflict. This might slightly increase the forwarding hit ration from the store buffer to the load buffer, while decreasing the latency of loads execution.
  localparam bit ENABLE_STORE_PRIO_2WAY_ARBITER = 1'b1;

  // If defined, instantiate a byte selector in the load buffer. All memory
  // accesses are aligned on 64 bits, and the selector picks the correct
  // word/halfword/byte from it the fetched doubleword.
  localparam bit ONLY_DOUBLEWORD_MEM_ACCESSES = 1'b0;

  // CSRs
  // ----
  // If defined, instantiate additional performance counters (mcycle and
  // minstret are always instantiated). See 'csrs.sv' to see what counters are
  // available in LEN5.
  localparam bit LEN5_CSR_HPMCOUNTERS_EN = 1'b1;
endpackage
