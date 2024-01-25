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
// File: csr_macros.svh
// Author: Michele Caon
// Date: 03/11/2021

`ifndef CSR_MACROS_
`define CSR_MACROS_

`include "len5_config.svh"

// -------------
// CSR ADDRESSES
// -------------

// PERFORMANCE COUNTERS
// --------------------
`define CSR_ADDR_CYCLE 12'hc00
`define CSR_ADDR_TIME 12'hc01
`define CSR_ADDR_INSTRET 12'hc02
`define CSR_ADDR_CYCLEH 12'hc80
`define CSR_ADDR_TIMEH 12'hc81
`define CSR_ADDR_INSTRETH 12'hc82

// USER SPACE
// ----------
// User trap setup
`define CSR_ADDR_USTATUS 12'h000
`define CSR_ADDR_UUIE 12'h004
`define CSR_ADDR_UTVEC 12'h005
// User trap handling 
`define CSR_ADDR_USCRATCH 12'h040
`define CSR_ADDR_UEPC 12'h041
`define CSR_ADDR_UCAUSE 12'h042
`define CSR_ADDR_UTVAL 12'h043
`define CSR_ADDR_UIP 12'h044
// User floating point
`define CSR_ADDR_FFLAGS 12'h001
`define CSR_ADDR_FRM 12'h002
`define CSR_ADDR_FCSR 12'h003

// SUPERVISOR
// ----------
// Supervisor trap setup
`define CSR_ADDR_SSTATUS 12'h100
`define CSR_ADDR_SEDELEG 12'h102
`define CSR_ADDR_SIDELEG 12'h103
`define CSR_ADDR_SIE 12'h104
`define CSR_ADDR_STVEC 12'h105
`define CSR_ADDR_SCOUNTEREN 12'h106
// Supervisor trap handling
`define CSR_ADDR_SSCRATCH 12'h140
`define CSR_ADDR_SEPC 12'h141
`define CSR_ADDR_SCAUSE 12'h142
`define CSR_ADDR_STVAL 12'h143
`define CSR_ADDR_SIP 12'h144
// SUPERVISOR PROTECTION AND TRANSLATION
`define CSR_ADDR_SATP 12'h180

// MACHINE
// -------
// Machine information CSRs
`define CSR_ADDR_MVENDORID 12'hf11
`define CSR_ADDR_MARCHID 12'hf12
`define CSR_ADDR_MIMPID 12'hf13
`define CSR_ADDR_MHARTID 12'hf14
// Machine trap setup
`define CSR_ADDR_MSTATUS 12'h300
`define CSR_ADDR_MISA 12'h301
`define CSR_ADDR_MEDELEG 12'h302
`define CSR_ADDR_MIDELEG 12'h303
`define CSR_ADDR_MIE 12'h304
`define CSR_ADDR_MTVEC 12'h305
`define CSR_ADDR_MCOUNTEREN 12'h306
// Machine trap handling
`define CSR_ADDR_MSCRATCH 12'h340
`define CSR_ADDR_MEPC 12'h341
`define CSR_ADDR_MCAUSE 12'h342
`define CSR_ADDR_MTVAL 12'h343
`define CSR_ADDR_MIP 12'h344
// Machine performance counters
`define CSR_ADDR_MCYCLE 12'hb00
`define CSR_ADDR_MINSTRET 12'hb02
`define CSR_ADDR_HPMCOUNTER3 12'hb03
`define CSR_ADDR_HPMCOUNTER4 12'hb04
`define CSR_ADDR_HPMCOUNTER5 12'hb05
`define CSR_ADDR_HPMCOUNTER6 12'hb06
`define CSR_ADDR_HPMCOUNTER7 12'hb07
`define CSR_ADDR_HPMCOUNTER8 12'hb08
`define CSR_ADDR_HPMCOUNTER9 12'hb09
`define CSR_ADDR_HPMCOUNTER10 12'hb0a
`define CSR_ADDR_HPMCOUNTER11 12'hb0b
`define CSR_ADDR_HPMCOUNTER12 12'hb0c
`define CSR_ADDR_HPMCOUNTER13 12'hb0d
`define CSR_ADDR_HPMCOUNTER14 12'hb0e
`define CSR_ADDR_HPMCOUNTER15 12'hb0f
`define CSR_ADDR_HPMCOUNTER16 12'hb10
`define CSR_ADDR_HPMCOUNTER17 12'hb11
`define CSR_ADDR_HPMCOUNTER18 12'hb12
`define CSR_ADDR_HPMCOUNTER19 12'hb13
`define CSR_ADDR_HPMCOUNTER20 12'hb14
`define CSR_ADDR_HPMCOUNTER21 12'hb15
`define CSR_ADDR_HPMCOUNTER22 12'hb16
`define CSR_ADDR_HPMCOUNTER23 12'hb17
`define CSR_ADDR_HPMCOUNTER24 12'hb18
`define CSR_ADDR_HPMCOUNTER25 12'hb19
`define CSR_ADDR_HPMCOUNTER26 12'hb1a
`define CSR_ADDR_HPMCOUNTER27 12'hb1b
`define CSR_ADDR_HPMCOUNTER28 12'hb1c
`define CSR_ADDR_HPMCOUNTER29 12'hb1d
`define CSR_ADDR_HPMCOUNTER30 12'hb1e
`define CSR_ADDR_HPMCOUNTER31 12'hb1f
// Machine counters setup
`define CSR_ADDR_MCOUNTERINHIBIT 12'h320
`define CSR_ADDR_MHPMEVENT3 12'h323
`define CSR_ADDR_MHPMEVENT4 12'h324
`define CSR_ADDR_MHPMEVENT5 12'h325
`define CSR_ADDR_MHPMEVENT6 12'h326
`define CSR_ADDR_MHPMEVENT7 12'h327
`define CSR_ADDR_MHPMEVENT8 12'h328
`define CSR_ADDR_MHPMEVENT9 12'h329
`define CSR_ADDR_MHPMEVENT10 12'h32a
`define CSR_ADDR_MHPMEVENT11 12'h32b
`define CSR_ADDR_MHPMEVENT12 12'h32c
`define CSR_ADDR_MHPMEVENT13 12'h32d
`define CSR_ADDR_MHPMEVENT14 12'h32e
`define CSR_ADDR_MHPMEVENT15 12'h32f
`define CSR_ADDR_MHPMEVENT16 12'h330
`define CSR_ADDR_MHPMEVENT17 12'h331
`define CSR_ADDR_MHPMEVENT18 12'h332
`define CSR_ADDR_MHPMEVENT19 12'h333
`define CSR_ADDR_MHPMEVENT20 12'h334
`define CSR_ADDR_MHPMEVENT21 12'h335
`define CSR_ADDR_MHPMEVENT22 12'h336
`define CSR_ADDR_MHPMEVENT23 12'h337
`define CSR_ADDR_MHPMEVENT24 12'h338
`define CSR_ADDR_MHPMEVENT25 12'h339
`define CSR_ADDR_MHPMEVENT26 12'h33a
`define CSR_ADDR_MHPMEVENT27 12'h33b
`define CSR_ADDR_MHPMEVENT28 12'h33c
`define CSR_ADDR_MHPMEVENT29 12'h33d
`define CSR_ADDR_MHPMEVENT30 12'h33e
`define CSR_ADDR_MHPMEVENT31 12'h33f

// --------------
// DEFAULT VALUES
// --------------

// MISA extensions
// ---------------
`ifdef LEN5_A_EN
`define MISA_EXT_A 1'b1 // atomic
`else
`define MISA_EXT_A 1'b0 // atomic
`endif  /* LEN5_A_EN */
`define MISA_EXT_B 1'b0 // bit (?)
`ifdef LEN5_C_EN
`define MISA_EXT_C 1'b1 // compressed
`else
`define MISA_EXT_C 1'b0 // compressed
`endif  /* LEN5_C_EN0 */
`ifdef LEN5_FP_EN
`define MISA_EXT_D 1'b1 // double float
`else
`define MISA_EXT_D 1'b0 // double float
`endif  /* LEN5_FP_EN */
`define MISA_EXT_E 1'b0 // RV32E base ISA
`ifdef LEN5_FP_EN
`define MISA_EXT_F 1'b1 // single float
`else
`define MISA_EXT_F 1'b0 // single float
`endif  /* LEN5_FP_EN */
`define MISA_EXT_G 1'b0 // other std extensions
`define MISA_EXT_H 1'b0 // reserved
`define MISA_EXT_I 1'b1 // RV32I/64I/128I base ISA
`define MISA_EXT_J 1'b0 // dynamically translated language (?)
`define MISA_EXT_K 1'b0 // reserved
`define MISA_EXT_L 1'b0 // decimal floating point (?)
`ifdef LEN5_M_EN
`define MISA_EXT_M 1'b1 // compressed
`else
`define MISA_EXT_M 1'b0 // compressed
`endif  /* LEN5_M_EN0 */
`define MISA_EXT_N 1'b0 // user level interrupt
`define MISA_EXT_O 1'b0 // reserved
`define MISA_EXT_P 1'b0 // packed SIMD (?)
`define MISA_EXT_Q 1'b0 // quad precision float
`define MISA_EXT_R 1'b0 // reserved
`define MISA_EXT_S 1'b0 // supervisor mode
`define MISA_EXT_T 1'b0 // transactional memory (?)
`define MISA_EXT_U 1'b0 // user mode
`ifdef LEN5_V_EN
`define MISA_EXT_V 1'b1 // vector (?)
`else
`define MISA_EXT_V 1'b0 // vector (?)
`endif  /* LEN5_V_EN */
`define MISA_EXT_W 1'b0 // reserved
`define MISA_EXT_X 1'b0 // non-standard extensions
`define MISA_EXT_Y 1'b0 // reserved
`define MISA_EXT_Z 1'b0 // reserved

`define MISA_EXT { \
    `MISA_EXT_A, \
    `MISA_EXT_B, \
    `MISA_EXT_C, \
    `MISA_EXT_D, \
    `MISA_EXT_E, \
    `MISA_EXT_F, \
    `MISA_EXT_G, \
    `MISA_EXT_H, \
    `MISA_EXT_I, \
    `MISA_EXT_J, \
    `MISA_EXT_K, \
    `MISA_EXT_L, \
    `MISA_EXT_M, \
    `MISA_EXT_N, \
    `MISA_EXT_O, \
    `MISA_EXT_P, \
    `MISA_EXT_Q, \
    `MISA_EXT_R, \
    `MISA_EXT_S, \
    `MISA_EXT_T, \
    `MISA_EXT_U, \
    `MISA_EXT_V, \
    `MISA_EXT_W, \
    `MISA_EXT_X, \
    `MISA_EXT_Y, \
    `MISA_EXT_Z \
}

// Implementation IDs
// ------------------
`define CSR_MVENDORID 'h0
`define CSR_MARCHID 'h0
`define CSR_MIMPID 'h0
`define CSR_MHARTID 'h0

// MTVEC
// -----
`define CSR_MTVEC_BASE 'h0
`define CSR_MTVEC_MODE 2'b00

`endif  /* CSR_MACROS_ */
