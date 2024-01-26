/* based on the work from ETH Zurich and University of Bologna */
/*
* Copyright 2019 ETH Zürich and University of Bologna
*
* Licensed under the Apache License, Version 2.0 (the "License");
* you may not use this file except in compliance with the License.
* You may obtain a copy of the License at
*
*     http://www.apache.org/licenses/LICENSE-2.0
*
* Unless required by applicable law or agreed to in writing, software
* distributed under the License is distributed on an "AS IS" BASIS,
* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
* See the License for the specific language governing permissions and
* limitations under the License.
*/

.section .vectors, "ax"
.option norvc
vector_table:
    j sw_irq_handler  	# all sync. exceptions, plus user-SW interrupt
    j __no_irq_handler  # supervisor software interrupt
    j __no_irq_handler	# [reserved for future standard use]
	j __no_irq_handler	# machine software interrupt
	j __no_irq_handler	# user timer interrupt
	j __no_irq_handler	# supervisor timer interrupt
	j __no_irq_handler	# [reserved for future standard use]
	j __no_irq_handler	# machine timer interrupt
	j __no_irq_handler	# user external interrupt
	j __no_irq_handler	# supervisor external interrupt
	j __no_irq_handler	# [reserved for future standard use]
	j __no_irq_handler	# machine external interrupt
	j __no_irq_handler	# [reserved for future standard use]
	j __no_irq_handler	# [reserved for future standard use]
	j __no_irq_handler	# [reserved for future standard use]
	j __no_irq_handler	# [reserved for future standard use]
	j __no_irq_handler	# , platform use - BEGIN
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j verification_irq_handler # |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# |
	j __no_irq_handler	# ' platform use - END

# Service routines
.section .text.vecs
/* exception handling */
__no_irq_handler:
	la a0, no_exception_handler_msg
	jal ra, puts
	j __no_irq_handler


sw_irq_handler:
	csrr t0, mcause
	slli t0, t0, 1  /* shift off the high bit */
	srli t0, t0, 1
	li t1, 2
	beq t0, t1, handle_illegal_insn
	li t1, 11
	beq t0, t1, handle_ecall
	li t1, 3
	beq t0, t1, handle_ebreak
	j handle_unknown

handle_ecall:
	la a0, ecall_msg
	jal ra, puts
	j end_handler

handle_ebreak:
	la a0, ebreak_msg
	jal ra, puts
	j end_handler

handle_illegal_insn:
	la a0, illegal_insn_msg
	jal ra, puts
	j end_handler

handle_unknown:
	la a0, unknown_msg
	jal ra, puts
	j end_handler

end_handler:
	csrr a0, mepc
	addi a0, a0, 4
	csrw mepc, a0
	mret
/* this interrupt can be generated for verification purposes, random or when the PC is equal to a given value*/
verification_irq_handler:
	mret

# Error messages
.section .rodata
illegal_insn_msg:
	.string "Illegal instruction exception handler entered\n"
ecall_msg:
	.string "ecall exception handler entered\n"
ebreak_msg:
	.string "ebreak exception handler entered\n"
unknown_msg:
	.string "Unknown exception handler entered\n"
no_exception_handler_msg:
	.string "No exception handler installed\n"