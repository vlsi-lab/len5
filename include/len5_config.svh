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
// File: len5_config.svh
// Author: Michele Caon
// Date: 04/11/2021

`ifndef LEN5_CONFIG_
`define LEN5_CONFIG_

// --------------------
// GLOBAL CONFIGURATION
// --------------------

// Boot memory translation mode
`define BOOT_VM_MODE BARE // BARE|SV39|SV48

// Boot program counter
`define BOOT_PC 64'h180

// MEMORY-MAPPED DEVICES
// ---------------------

// Address mask for memory-mapped devices
// This mask defines the address range that is reserved to memory-mapped
// devices. Store-to-load forwarding (see below) in this region is not 
// performed.
`define MMAP_MASK 64'h000000000000ffff // 64kiB by default

// TB Serial interface base address
`define SERIAL_ADDR 'h100

// TB exit register address (stop the simulation when written)
`define EXIT_ADDR 'h200

// MEMORY EMULATOR PARAMETERS
// --------------------------

// Raise access fault on load from empty (uninitialized) memory location
//`define MEM_EMU_RAISE_READ_ACCESS_FAULT

// Skip instruction and/or data output registers
`define MEM_EMU_SKIP_INSTR_OUT_REG
`define MEM_EMU_SKIP_DATA_OUT_REG

// FRONTEND PARAMETERS
// -------------------
// BPU g-share predictor global history length
`define BPU_HLEN 4

// BPU g-share predictor counters initial value
// NOTE: must one of {SNT, WNT, WT, ST}
`define BPU_INIT_C2B WT

// BPU Branch Target Buffer (BTB) addressing bits (the remaining ones are used
// as tag)
`define BPU_BTB_BITS 4

// -----------------
// PIPELINE SWITCHES
// -----------------
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
`define SKIP_FETCH_MEMIF_REQ_SPILL_CELL // memory requests from the fetch unit are directly passed to the memory
//`define SKIP_FETCH_MEMIF_ANS_SPILL_CELL // fetched instructions are directly passed to the issue stage 

// EXECUTION PIPELINE
// ------------------

// ALU
`define SKIP_ALU_SPILL_CELL // make the ALU fully combinational

// Branch Unit
`define SKIP_BU_ADDER_SPILL_CELL // make the target address adder fully combinational

// Load-store Unit
`define SKIP_LSU_ADDER_SPILL_CELL // make address adder fully combinational

// Commit Stage
`define SKIP_COMMIT_SPILL_CELL // directly connect the commit CU to the ROB output

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
`define LEN5_STORE_LOAD_FWD_EN

// Enable C extension
// ------------------
// NOTE: CURRENTLY UNSUPPORTED
//`define LEN5_C_EN

// Enable M extension support
// --------------------------
//`define LEN5_M_EN

// Enable floating-point support
// -----------------------------
//`define LEN5_FP_EN

// Enable atomic support
// ---------------------
//`define LEN5_A_EN

// Reservation stations
// --------------------
// If defined, the arbiters of the shared virtual address adder, the DTLB and the DCACHE will give the highest priority to the store buffer in case of conflict. This might slightly increase the forwarding hit ration from the store buffer to the load buffer, while decreasing the latency of loads execution. 
`define ENABLE_STORE_PRIO_2WAY_ARBITER

// If defined, instantiate a byte selector in the load buffer. All memory
// accesses are aligned on 64 bits, and the selector picks the correct
// word/halfword/byte from it the fetched doubleword.
//`define ONLY_DOUBLEWORD_MEM_ACCESSES

// CSRs
// ----
// If defined, instantiate additional performance counters (mcycle and 
// minstret are always instantiated). See 'csrs.sv' to see what counters are
// available in LEN5.
`define LEN5_CSR_HPMCOUNTERS_EN

//////////////////////////////////////////////////////////////////////////////
// OTHER DEFINES
`define ST2LD_FWD_MASK ~`MMAP_MASK

// CONSTRUCT PARAMETERS FROM DEFINES
`ifdef MEM_EMU_SKIP_INSTR_OUT_REG
localparam MEM_EMU_SKIP_INSTR_OUT_REG = 1;
`else
localparam MEM_EMU_SKIP_INSTR_OUT_REG = 0;
`endif  /* MEM_EMU_SKIP_INSTR_OUT_REG */
`ifdef MEM_EMU_SKIP_DATA_OUT_REG
localparam MEM_EMU_SKIP_DATA_OUT_REG = 1;
`else
localparam MEM_EMU_SKIP_DATA_OUT_REG = 0;
`endif  /* MEM_EMU_SKIP_DATA_OUT_REG */

`ifdef SKIP_FETCH_MEMIF_REQ_SPILL_CELL
localparam FETCH_REQ_SPILL_SKIP = 1;
`else
localparam FETCH_REQ_SPILL_SKIP = 0;
`endif  /* SKIP_FETCH_MEMIF_REQ_SPILL_CELL */
`ifdef SKIP_FETCH_MEMIF_ANS_SPILL_CELL

localparam FETCH_ANS_SPILL_SKIP = 1;
`else
localparam FETCH_ANS_SPILL_SKIP = 0;
`endif  /* SKIP_FETCH_MEMIF_ANS_SPILL_CELL */

`ifdef SKIP_ALU_SPILL_CELL
localparam ALU_SPILL_SKIP = 1;
`else
localparam ALU_SPILL_SKIP = 0;
`endif  /* SKIP_ALU_SPILL_CELL */

`ifdef SKIP_BU_ADDER_SPILL_CELL
localparam BU_SPILL_SKIP = 1;
`else
localparam BU_SPILL_SKIP = 0;
`endif  /* SKIP_BU_ADDER_SPILL_CELL */

`ifdef SKIP_LSU_ADDER_SPILL_CELL
localparam LSU_SPILL_SKIP = 1;
`else
localparam LSU_SPILL_SKIP = 0;
`endif  /* SKIP_LSU_ADDER_SPILL_CELL */

`ifdef SKIP_COMMIT_SPILL_CELL
localparam COMMIT_SPILL_SKIP = 1;
`else
localparam COMMIT_SPILL_SKIP = 0;
`endif  /* SKIP_COMMIT_SPILL_CELL */

`endif  /* LEN5_CONFIG_ */
