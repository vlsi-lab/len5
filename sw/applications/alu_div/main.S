.section .text
.global main
.balign 4

main:
    addi t0, zero, 15
    addi t1, zero, 12
    addi t2, zero, 3
    div t3,t0,t2    # t3 = 5
    divu t4,t1,t2   # t4 = 4
    remw t5,t0,t2   # t5 = 0
    remuw t5,t4,t1  # t5 = 4
    rem t6,t0,t5    # t6 = 3 forwarding from previous result 
    #sub t4,t1,t0
    #slli t3,t1,1
    #add t3,t0,t1
    # load immediate from registers
    # do a multiplication
    # store result
    sd t3, 136(x0)
    ld t0, 136(x0)  # t0=5
    addw t3,t2,t0   # t3= 8
    add t3,t3,t1    # t3 = 20 
    remw t6,t0,t5   # t6 = 1 
    divw t4,t3,t2   # t4 = 6
    remu t4,t3,t4   # t4 = 2 forwarding from previous result
    divuw t5,t0,t4  # t5 = 2 forwarding from previous result
    remuw t6,t1,t4  # t6 = 0  
    ret
