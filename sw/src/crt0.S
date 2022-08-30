# Switches and macros
#include "len5.h"

# Bare-metal entry point
.section .init, "ax"
.global _start
_start:
    .cfi_startproc
    .cfi_undefined ra

    # Initialize global pointer
    .option push
    .option norelax
    la gp, __global_pointer$ # 
    .option pop

    # Clear the bss segment
    la a0, _edata # 
    la a2, _end # 
    sub a2, a2, a0 # a2 = a2 - a0
    li a1, 0 # a1 = 0
    jal zero, memset

    # Ctors and dtors
    la a0, __libc_fini_array # 
    jal zero, atexit
    jal zero, __libc_init_array

    # Initialize stack pointer
    la sp, __stack_top # provided by linker script
    add s0, sp, zero; # s0 = sp + zero

    # Call main
    lw a0, 0(sp) # a0 = argc
    addi a1, sp, __SIZEOF_POINTER__; # a1 = sp + __SIZEOF_POINTER__ (a1 = argv)
    li a2, 0 # a2 = 0
    call main  # jump to main and save position to ra
    tail exit
    .cfi_endproc
    .end
