# Copyright 2022 Politecnico di Torino.
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 2.0 (the "License"); you may not use this file except in
# compliance with the License. You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
# File: crt0.S
# Author: Michele Caon
# Date: 15/09/2022

# NOTE: this file is based on Newlib (libgloss) crt0 implementation

# Switches and macros
#include "len5_switches.h"

# Bare-metal entry point
.section .text.start, "ax"
.global _start
_start:
    .cfi_startproc
    .cfi_undefined ra

    # Initialize global pointer
    .option push
    .option norelax
    la gp, __global_pointer$ # 
    .option pop

    # Initialize stack pointer
    la sp, __stack_top # provided by linker script
    mv  s0, sp # s0 = sp

    # Setup 'mtvec' CSR to vectored exception mode
    la a0, __vector_start # base address, provided by linker script 
    addi a0, a0, 0x1 # a0 = a0 | 0x1 (enable vectored mode)
    csrw mtvec, a0

    # Clear the bss segment
    la a0, _edata # bss sections begin (from linker script)
    la a2, _end # bss sections end (from linker script)
    sub a2, a2, a0 # a2 = a2 - a0
    li a1, 0 # a1 = 0
    call memset

    # Ctors and dtors
#ifndef LEN5_SKIP_CRT0_LIBC_INIT_ARRAY
    la a0, __libc_fini_array # register global termination functions
    call atexit # to be called upon exit
    call __libc_init_array # Run global initialization functions
#endif

    # Call main
    lw a0, 0(sp) # a0 = argc
    addi a1, sp, __SIZEOF_POINTER__ # a1 = argv
    li a2, 0 # a2 = 0 (envp = NULL)
    call main  # jump to main and save position to ra
    tail exit
    
    .cfi_endproc
    .end

.global _init
.global _fini
_init:
_fini:
    /* These don't have to do anything since we use init_array/fini_array */
	ret