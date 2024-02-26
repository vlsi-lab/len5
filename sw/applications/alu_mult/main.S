.section .text
.global main
.balign 4

main:
    addi t0, zero, 15
    addi t1, zero, 12
    addi t2, zero, 3
    mul t3,t2,t0    #t3=45
    mulh t4,t0,t1   #t4=0
    mul t5,t4,t0    #t5=0 t4 dep
    mulw t6,t2,t3    #t6=135 t3 data dep
    sd t1, 136(x0)
    ld t0, 136(x0)   #t0=12
    addi t1, t1, 12  #t1=24
    mulw t3,t2,t0    #t3=36
    mul t3,t1,t0     #t3=288
    addi t1, t1, 12  #t1=36
    addi t2, t2, 3   #t2=6
    mulhu t4,t2,t1   #t4=0
    mul t3,t6,t0     #t3=1620
    mulw t4,t2,t2    #t4=36
    mulw t4,t0,t2    #t4=72
    mulw t6,t3,t4    #t6=116640
    mulw  t4,t6,t6    #t4=
    mulw  t5,t2,t1    #t5=
    
    ret
