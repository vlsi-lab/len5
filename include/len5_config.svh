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
`define LEN5_CONFIG

// --------------------
// GLOBAL CONFIGURATION
// --------------------

// Boot memory translation mode
`define BOOT_VM_MODE BARE // BARE|SV39|SV48

// FRONTEND PARAMETERS
// -------------------

// Boot program counter
`define BOOT_PC 'h800f8

// BPU g-share predictor global history length
`define BPU_HLEN 4

// BPU g-share predictor counters initial value
// NOTE: must one of {SNT, WNT, WT, ST}
`define BPU_INIT_C2B WNT

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
// `define SKIP_FETCH_MEMIF_ANS_SPILL_CELL // fetched instructions are directly passed to the issue stage 

// EXECUTION PIPELINE
// ------------------

// Branch Unit
`define SKIP_BU_ADDER_SPILL_CELL    // make the target address adder fully combinational

// Load-store Unit
`define SKIP_LSU_ADDER_SPILL_CELL   // make address adder fully combinational

// Commit Stage
`define SKIP_COMMIT_SPILL_CELL      // directly connect the commit CU to the ROB output

// ----------------
// FEATURE SWITCHES
// ----------------

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

// Enable privileged instructions support
// --------------------------------------
//`define LEN5_PRIVILEGED_EN

// Reservation stations
// --------------------
// Enable age-based selectors in the reservation station. If not defined, simple fixed priority encoders will be used instead. This should lead to worse performance in terms of latency (and possibly throughput with certain code sequences) while reducing area and power consumption
//`define ENABLE_AGE_BASED_SELECTOR

// If defined, the arbiters of the shared virtual address adder, the DTLB and the DCACHE will give the highest priority to the store buffer in case of conflict. This might slightly increase the forwarding hit ration from the store buffer to the load buffer, while decreasing the latency of loads execution. 
`define ENABLE_STORE_PRIO_2WAY_ARBITER

// If defined, instantiate a byte selector in the load buffer. All memory
// accesses are aligned on 64 bits, and the selector picks the correct
// word/halfword/byte from it the fetched doubleword.
//`define ONLY_DOUBLEWORD_MEM_ACCESSES

//////////////////////////////////////////////////////////////////////////////
// CONSTRUCT PARAMETERS FROM DEFINES

`ifdef SKIP_FETCH_MEMIF_REQ_SPILL_CELL
localparam  FETCH_REQ_SPILL_SKIP = 1;
`else
localparam  FETCH_REQ_SPILL_SKIP = 0;
`endif /* SKIP_FETCH_MEMIF_REQ_SPILL_CELL */
`ifdef SKIP_FETCH_MEMIF_ANS_SPILL_CELL

localparam  FETCH_ANS_SPILL_SKIP = 1;
`else
localparam  FETCH_ANS_SPILL_SKIP = 0;
`endif /* SKIP_FETCH_MEMIF_ANS_SPILL_CELL */

`ifdef SKIP_LSU_ADDER_SPILL_CELL
localparam LSU_SPILL_SKIP = 1;
`else
localparam LSU_SPILL_SKIP = 0;
`endif /* SKIP_LSU_ADDER_SPILL_CELL */

`ifdef SKIP_BU_ADDER_SPILL_CELL
localparam BU_SPILL_SKIP = 1;
`else
localparam BU_SPILL_SKIP = 0;
`endif /* SKIP_BU_ADDER_SPILL_CELL */

`ifdef SKIP_COMMIT_SPILL_CELL
localparam COMMIT_SPILL_SKIP = 1;
`else
localparam COMMIT_SPILL_SKIP = 0;
`endif /* SKIP_COMMIT_SPILL_CELL */

`endif /* LEN5_CONFIG_ */