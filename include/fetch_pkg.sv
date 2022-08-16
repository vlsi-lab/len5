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

// LEN5 compilation switches
`include "len5_config.svh"

package fetch_pkg;
    import len5_pkg::XLEN;
    import len5_pkg::except_code_t;

    // ----------
    // PARAMETERS
    // ----------

    // g-share branch predictor history length
    localparam  HLEN = 4;

    // Branch target buffer bits 
    localparam  BTB_BITS = 4;

    // ----------
    // DATA TYPES
    // ----------

    // instruction selector enums
    typedef enum logic [1:0] { current_pc = 'h0, prev_pc = 'h1, line_pc = 'h2 } pc_src_t;
    typedef enum logic [1:0] { cache_out = 'h0, line_reg = 'h1, line_bak = 'h2 } line_src_t;

    // prediction structure
    typedef struct packed {
        logic [XLEN-1:0]  pc;
        logic [XLEN-1:0]  target;
        logic             taken;
    } prediction_t;

    // resolution structure
    typedef struct packed {
        logic [XLEN-1:0]  pc;
        logic [XLEN-1:0]  target;
        logic             taken;
        logic             mispredict;
    } resolution_t;

    // Memory interface answer spill cell data type
    typedef struct packed {
        logic [XLEN-1:0]    instr;
        logic [XLEN-1:0]    addr;
        logic               except_raised;
        except_code_t       except_code;
    } mem_if_ans_reg_t;

endpackage

`endif /* FETCH_PKG_SVH_ */

