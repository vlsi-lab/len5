.section .text
.global main
.balign 4

main:
    addi t0, zero, 15
    sd t1, 136(x0)
    ld t0, 136(x0)
    ret
