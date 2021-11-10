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
`define BOOT_PC 'h0

// --------------------
// COMPILATION SWITCHES
// --------------------

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

// LOAD-STORE UNIT
// If defined, the arbiters of the shared virtual address adder, the DTLB and the DCACHE will give the highest priority to the store buffer in case of conflict. This might slightly increase the forwarding hit ration from the store buffer to the load buffer, while decreasing the latency of loads execution. 
`define ENABLE_STORE_PRIO_2WAY_ARBITER

`endif /* LEN5_CONFIG_ */