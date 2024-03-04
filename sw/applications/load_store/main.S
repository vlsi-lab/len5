.section .text
.global main
.balign 4

main:
    addi sp, sp, -8
    li t0, 15
    sd t0, 0(sp)
    ld t1, 0(sp)
    addi sp, sp, 8
    ret
