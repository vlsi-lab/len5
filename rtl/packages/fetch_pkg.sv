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
// File: fetch_pkg.sv
// Author: Michele Caon
// Date: 04/08/2022

`ifndef FETCH_PKG_SVH_
`define FETCH_PKG_SVH_

package fetch_pkg;
  import len5_config_pkg::*;
  import len5_pkg::XLEN;
  import len5_pkg::ILEN;
  import len5_pkg::except_code_t;

  // ----------
  // DATA TYPES
  // ----------

  // BPU G-share predictor counter values and initial value
  typedef enum logic [1:0] {  // 2-bit counter
    SNT,  // strong not-taken
    WNT,  // weak not-taken
    WT,   // weak taken
    ST    // strong taken
  } c2b_t;

  // instruction selector enums
  typedef enum logic [1:0] {
    current_pc = 'h0,
    prev_pc = 'h1,
    line_pc = 'h2
  } pc_src_t;
  typedef enum logic [1:0] {
    cache_out = 'h0,
    line_reg  = 'h1,
    line_bak  = 'h2
  } line_src_t;

  // prediction structure
  typedef struct packed {
    logic [XLEN-1:0] pc;
    logic [XLEN-1:0] target;
    logic            taken;
  } prediction_t;

  // resolution structure
  typedef struct packed {
    logic [XLEN-1:0] pc;
    logic            mispredict;
    logic            taken;
    logic [XLEN-1:0] target;
  } resolution_t;

  // Memory interface answer spill cell data type
  typedef struct packed {
    logic [ILEN-1:0] instr;
    prediction_t     pred_data;
    logic            except_raised;
    except_code_t    except_code;
  } mem_if_ans_reg_t;

  // ----------
  // PARAMETERS
  // ----------

  // Instruction address offset
  localparam int unsigned OFFSET = $clog2(
      ILEN / 8
  );  // 2 LSB of addresses are always 0, so no use in using them for indexing

  // G-share branch predictor history length and counters intial value
  localparam int unsigned HLEN = BPU_HLEN;
  localparam c2b_t INIT_C2B = WT;

  // Branch target buffer bits
  localparam int unsigned BTB_BITS = BPU_BTB_BITS;

endpackage

`endif  /* FETCH_PKG_SVH_ */

