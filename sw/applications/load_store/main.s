.global main
main:
    addi x1, zero, 15
    sd x1, 136(x0)
    ld x2, 136(x0)
