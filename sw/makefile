####################
# ----- INFO ----- #
####################
# Set up LEN5 toolchain settings and build source files

# VARIABLES
# ---------
# LEN5 root directory
ROOT 			= ..

# LEN5 software libraries
BUILD_DIR		?= $(ROOT)/build
SW_BUILD_DIR 	:= $(BUILD_DIR)/sw
SW_DIR			:= $(ROOT)/sw
LEN5_LIB 		:= $(SW_BUILD_DIR)/lib/liblen5.a
LIB_SRCS		:= $(shell find $(SW_DIR)/src -type f -name *.c -or -name *.s -or -name *.S)
LIB_OBJS		:= $(filter %.o,\
				   $(patsubst $(SW_DIR)/src/%.c,$(SW_BUILD_DIR)/obj/%.o,$(LIB_SRCS))\
				   $(patsubst $(SW_DIR)/src/%.s,$(SW_BUILD_DIR)/obj/%.o,$(LIB_SRCS))\
				   $(patsubst $(SW_DIR)/src/%.S,$(SW_BUILD_DIR)/obj/%.o,$(LIB_SRCS)))

# LEN5 software support
SW_SUPP_SRCS	:= $(SW_DIR)/src/crt0.S \
				   $(SW_DIR)/src/irq.S \
				   $(SW_DIR)/src/syscall.c
SW_SUPP_INCS 	:= $(wildcard $(SW_DIR)/include/*.h) \
				   $(SW_DIR)/len5-sim.ld \
				   $(SW_DIR)/len5-qemu.ld
BUILD_SUPP		:= $(patsubst $(SW_DIR)/%,$(SW_BUILD_DIR)/%,$(SW_SUPP_INCS))
LD_SCRIPT		:= $(SW_BUILD_DIR)/len5-sim.ld
QEMU_LD_SCRIPT	:= $(SW_BUILD_DIR)/len5-qemu.ld

# Test programs
TEST_BUILD_DIR	:= $(SW_BUILD_DIR)/tests
TEST_DIR 		:= test-programs
TEST_SRCS		:= $(shell find $(TEST_DIR)/src/ -name '*.c' -or -name '*.s')
TESTS			:= $(addprefix tests/,$(basename $(notdir $(TEST_SRCS))))

# Custom source files

# RISC-V C compiler
CROSS_COMPILE 	?= riscv64-unknown-elf-
ISA_STRING		?= rv64i
ABI_STRING		?= lp64
CC 				:= $(CROSS_COMPILE)gcc
CFLAGS			:= 	-march=$(ISA_STRING) \
					-mabi=$(ABI_STRING) \
					-ffreestanding \
					-O1 \
					-Wall
QEMU_CFLAGS		:= 	-march=$(ISA_STRING) \
					-mabi=$(ABI_STRING) \
					-mcmodel=medany \
					-ffreestanding \
					-O0 \
					-g \
					-D"UART_BASE=(unsigned char *)0x10000000"
CINC			:= -I$(SW_BUILD_DIR)/include -I$(TEST_DIR)/include
LDFLAGS			:= -nostartfiles \
				   -static \
				   -Wl,--gc-sections
AS 				:= $(CROSS_COMPILE)as
ASFLAGS			:= $(CFLAGS)
AR 				:= $(CROSS_COMPILE)ar
ARFLAGS			:= rcus # s replaces ranlib
OBJDUMP			:= $(CROSS_COMPILE)objdump
OBJCOPY			:= $(CROSS_COMPILE)objcopy

###########################
# ----- BUILD RULES ----- #
###########################

# Aliases
.PHONY: all, test-programs
all: test-programs
test-programs: $(TESTS)

# Test programs
# -------------
$(TESTS): tests/%: $(TEST_BUILD_DIR)/mem/%.img $(TEST_BUILD_DIR)/dis/%.dis $(TEST_BUILD_DIR)/qemu/%.elf $(TEST_BUILD_DIR)/qemu/%.dis

# Preserve intermediate files
.PRECIOUS: $(TEST_BUILD_DIR)/obj/%.o $(TEST_BUILD_DIR)/dis/%.dis $(TEST_BUILD_DIR)/bin/%.elf $(TEST_BUILD_DIR)/qemu/%.elf

# Memory image (for FPGA or RTL simulation)
$(TEST_BUILD_DIR)/mem/%.img: $(TEST_BUILD_DIR)/bin/%.elf | $(TEST_BUILD_DIR)/mem
	$(OBJCOPY) -O binary $< $@

# Disassembled source
$(TEST_BUILD_DIR)/dis/%.dis: $(TEST_BUILD_DIR)/bin/%.elf | $(TEST_BUILD_DIR)/dis
	$(OBJDUMP) -D -M numeric $< > $@
$(TEST_BUILD_DIR)/qemu/%.dis: $(TEST_BUILD_DIR)/qemu/%.elf | $(TEST_BUILD_DIR)/dis
	$(OBJDUMP) -D $< > $@

# LEN5 executable
$(TEST_BUILD_DIR)/bin/%.elf: $(TEST_BUILD_DIR)/obj/%.o $(LEN5_LIB) | $(TEST_BUILD_DIR)/bin
	$(CC) $(CFLAGS) $(CINC) -T $(LD_SCRIPT) $(LDFLAGS) -L$(SW_BUILD_DIR)/lib $< -o $@ -llen5

# Objects
$(TEST_BUILD_DIR)/obj/%.o: $(TEST_DIR)/src/%.c $(BUILD_SUPP) | $(TEST_BUILD_DIR)/obj .check-riscv
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@
$(TEST_BUILD_DIR)/obj/%.o: $(TEST_DIR)/src/%.S $(BUILD_SUPP) | $(TEST_BUILD_DIR)/obj .check-riscv
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@
$(TEST_BUILD_DIR)/obj/%.o: $(TEST_DIR)/src/%.s $(BUILD_SUPP) | $(TEST_BUILD_DIR)/obj .check-riscv
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@

# Debuggable QEMU executable
$(TEST_BUILD_DIR)/qemu/%.elf: $(TEST_DIR)/src/%.c | $(TEST_BUILD_DIR)/qemu
	$(CC) $(QEMU_CFLAGS) -mcmodel=medany $(CINC) -O0 -g -T $(QEMU_LD_SCRIPT) $(LDFLAGS) $(SW_SUPP_SRCS) $< -o $@
$(TEST_BUILD_DIR)/qemu/%.elf: $(TEST_DIR)/src/%.s | $(TEST_BUILD_DIR)/qemu
	$(CC) $(QEMU_CFLAGS) -mcmodel=medany $(CINC) -O0 -g -T $(QEMU_LD_SCRIPT) $(LDFLAGS) $(SW_SUPP_SRCS) $< -o $@
$(TEST_BUILD_DIR)/qemu/%.elf: $(TEST_DIR)/src/%.S | $(TEST_BUILD_DIR)/qemu
	$(CC) $(QEMU_CFLAGS) -mcmodel=medany $(CINC) -O0 -g -T $(QEMU_LD_SCRIPT) $(LDFLAGS) $(SW_SUPP_SRCS) $< -o $@

# Software support files (crt0, _write, headers)
$(BUILD_SUPP): $(SW_BUILD_DIR)/%: $(SW_DIR)/% | $(SW_BUILD_DIR)/include
	cp $< $@
$(LEN5_LIB): $(LIB_OBJS) | $(SW_BUILD_DIR)/lib
	$(AR) $(ARFLAGS) $@ $+

# Implicit compilation rules
$(SW_BUILD_DIR)/obj/%.o: $(SW_DIR)/src/%.c | $(SW_BUILD_DIR)/obj .check-riscv
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@
$(SW_BUILD_DIR)/obj/%.o: $(SW_DIR)/src/%.S | $(SW_BUILD_DIR)/obj .check-riscv
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@
$(SW_BUILD_DIR)/obj/%.o: $(SW_DIR)/src/%.s | $(SW_BUILD_DIR)/obj .check-riscv
	$(AS) $(ASFLAGS) $(CINC) -c $< -o $@

# Utils
# -----
# Check if RISC-V toolchain is in PATH
.PHONY: .check-riscv
.check-riscv:
	@if [ ! `which $(CC)` ]; then \
	printf -- "### ERROR: '$(CC)' is not in PATH.\n" >&2; \
	exit 1; fi

# Directories
# -----------
$(SW_BUILD_DIR)/obj $(SW_BUILD_DIR)/lib $(SW_BUILD_DIR)/include:
	mkdir -p $@
$(TEST_BUILD_DIR) $(TEST_BUILD_DIR)/obj $(TEST_BUILD_DIR)/bin $(TEST_BUILD_DIR)/dis $(TEST_BUILD_DIR)/mem $(TEST_BUILD_DIR)/qemu:
	mkdir -p $@

# Clear rules
# -----------
.PHONY: clean
clean: 
	$(RM) -r $(SW_BUILD_DIR)

.test:
	@echo $(LIB_OBJS)