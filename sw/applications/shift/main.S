.section .text
.global main
.balign 4

main:
    li t0, -1
    li t1, 5
    srlw t2, t0, t1
    ret
