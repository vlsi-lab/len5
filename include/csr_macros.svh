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

// -------------
// CSR ADDRESSES
// -------------

// PERFORMANCE COUNTERS
// --------------------
`define CSR_ADDR_CYCLE      12'hc00
`define CSR_ADDR_TIME       12'hc01
`define CSR_ADDR_INSTRET    12'hc02
`define CSR_ADDR_CYCLEH     12'hc80
`define CSR_ADDR_TIMEH      12'hc81
`define CSR_ADDR_INSTRETH   12'hc82

// USER SPACE
// ----------
// User trap setup
`define CSR_ADDR_USTATUS    12'h000
`define CSR_ADDR_UUIE       12'h004
`define CSR_ADDR_UTVEC      12'h005
// User trap handling 
`define CSR_ADDR_USCRATCH   12'h040
`define CSR_ADDR_UEPC       12'h041
`define CSR_ADDR_UCAUSE     12'h042
`define CSR_ADDR_UTVAL      12'h043
`define CSR_ADDR_UIP        12'h044
// User floating point
`define CSR_ADDR_FFLAGS     12'h001
`define CSR_ADDR_FRM        12'h002
`define CSR_ADDR_FCSR       12'h003

// SUPERVISOR
// ----------
// Supervisor trap setup
`define CSR_ADDR_SSTATUS    12'h100
`define CSR_ADDR_SEDELEG    12'h102
`define CSR_ADDR_SIDELEG    12'h103
`define CSR_ADDR_SIE        12'h104
`define CSR_ADDR_STVEC      12'h105
`define CSR_ADDR_SCOUNTEREN 12'h106
// Supervisor trap handling
`define CSR_ADDR_SSCRATCH   12'h140
`define CSR_ADDR_SEPC       12'h141
`define CSR_ADDR_SCAUSE     12'h142
`define CSR_ADDR_STVAL      12'h143
`define CSR_ADDR_SIP        12'h144
// SUPERVISOR PROTECTION AND TRANSLATION
`define   CSR_ADDR_SATP       12'h180

// MACHINE
// -------
// Machine information CSRs
`define CSR_ADDR_MVENDORID  12'hf11
`define CSR_ADDR_MARCHID    12'hf12
`define CSR_ADDR_MIMPID     12'hf13
`define CSR_ADDR_MHARTID    12'hf14
// Machine trap setup
`define CSR_ADDR_MSTATUS    12'h300
`define CSR_ADDR_MISA       12'h301
`define CSR_ADDR_MEDELEG    12'h302
`define CSR_ADDR_MIDELEG    12'h303
`define CSR_ADDR_MIE        12'h304
`define CSR_ADDR_MTVEC      12'h305
`define CSR_ADDR_MCOUNTEREN 12'h306
// Machine trap handling
`define CSR_ADDR_MSCRATCH   12'h340
`define CSR_ADDR_MEPC       12'h341
`define CSR_ADDR_MCAUSE     12'h342
`define CSR_ADDR_MTVAL      12'h343
`define CSR_ADDR_MIP        12'h344

`endif /* CSR_MACROS_ */