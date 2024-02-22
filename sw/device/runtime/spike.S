# Support host interaction for the Spike ISA simulator

# A write to `tohost` with a 0 LSB will terminate the simulation
# returning the error message in the 31:1 bits to the host.

.section .tohost, "aw", @progbits

.align 6
.global tohost
tohost: .dword 0

.align 6
.global fromhost
fromhost: .dword 0

# Exit code is expected in a0
.global tohost_exit
tohost_exit:
    slli a0, a0, 1
    ori a0, a0, 1
    la t0, tohost
    sd a0, 0(t0)
    1: j 1b
