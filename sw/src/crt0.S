# Switches and macros
#include "len5.h"

.section .init, "ax"
.text
.global _start
_start:
    .cfi_startproc
    .cfi_undefined ra
    # Initialize global pointer
    .option push
    .option norelax
    la gp, __global_pointer$ # 
    .option pop
#ifdef LEN5_CRT0_INIT_BSS
    # Clear the bss segment
    la a0, _edata # 
    la a2, _end # 
    sub a2, a2, a0 # a2 = a2 - a0
    li a1, 0 # a1 = 0
    jal zero, memset
    la a0, __libc_fini_array # 
    jal zero, atexit
    jal zero, __libc_fini_array
#endif
    # Initialize stack pointer
    la sp, __stack_top # provided by linker script
    add s0, sp, zero; # s0 = sp + zero
    # Call main
    jal zero, main  # jump to zero, main and save position to ra
    .cfi_endproc
    .end
