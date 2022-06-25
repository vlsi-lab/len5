####################
# ----- INFO ----- #
####################

# Compile base LEN5 source files

# VARIABLES
# ---------

# Set Bash as default shell ('source' allows passing options to sourced scrips)
SHELL			:= /bin/bash

# Paths
ROOT 			:= ..
BUILD_DIR 		?= $(ROOT)/private/build
VLIB 			?= $(BUILD_DIR)/len5

# LEN5 test files
TEST_DIR		:= $(ROOT)/test-files
TEST_SRCS		:= $(shell find $(TEST_DIR)/src/ -name '*.c' -or -name '*.s')
TESTS			:= $(basename $(notdir $(TEST_SRCS)))
TEST_MEM		:= $(addprefix $(TEST_DIR)/mem/,$(TESTS:%=%.txt))
AWK_FORMAT 		:= $(ROOT)/scripts/awk-mem-format.txt

# LEN5 HDL files
GLOBAL_OPT		:= $(ROOT)/config/global-opt.f
PKG_OPT			:= $(ROOT)/config/pkg-opt.f
SRC_OPT			:= $(ROOT)/config/src-opt.f
TB_OPT			:= $(ROOT)/config/tb-opt.f

# SystemVerilog compiler
ifeq (, $(shell which vlog))
$(error 'vlog' is not in PATH. Did you run the initialization script?)
endif
VLOG			:= vlog -work $(VLIB) -svinputport=compat -f $(GLOBAL_OPT)
VLOG 			+= $(VLOG_ARGS)

# RISC-V C compiler
CROSS_COMPILE 	?= riscv64-unknown-elf-
ISA_STRING		:= rv64im
ABI_STRING		:= lp64
CC 				:= $(CROSS_COMPILE)gcc
CFLAGS			:= -march=$(ISA_STRING) -mabi=$(ABI_STRING)
AS 				:= $(CROSS_COMPILE)as
ASFLAGS			:= $(CFLAGS)
OBJDUMP			:= $(CROSS_COMPILE)objdump

###########################
# ----- BUILD RULES ----- #
###########################

# Files
# -----

.PHONY: all
all: tb test-files

# Packages
.PHONY: packages
packages: $(VLIB)
	@echo "Compiling LEN5 packages..."
	$(VLOG) -F $(PKG_OPT)

# Source files
.PHONY: source-files
source-files: packages
	@echo "Compiling LEN5 source files..."
	$(VLOG) -F $(SRC_OPT)

# Testbench
.PHONY: tb
tb: source-files
	@echo "Compiling LEN5 testbench files..."
	$(VLOG) -F $(TB_OPT)

# Test memory files
.PHONY: test-files
test-files: $(TEST_MEM)

.PRECIOUS: $(TEST_DIR)/dump/%.dump $(TEST_DIR)/obj/%.o
$(TEST_DIR)/mem/%.txt: $(TEST_DIR)/dump/%.dump | $(TEST_DIR)/mem
	awk '/[ ]+[0-9a-f]+:\t[0-9a-f]{8}/' $< | awk -f $(AWK_FORMAT) > $@
$(TEST_DIR)/dump/%.dump: $(TEST_DIR)/obj/%.o | $(TEST_DIR)/dump
	$(OBJDUMP) -M numeric -M no-aliases -d -j .text $< > $@
$(TEST_DIR)/obj/%.o: $(TEST_DIR)/src/%.c | $(TEST_DIR)/obj
	$(CC) $(CFLAGS) -c $< -o $@
$(TEST_DIR)/obj/%.o: $(TEST_DIR)/src/%.s | $(TEST_DIR)/obj
	$(AS) $(ASFLAGS) -c $< -o $@

# QuestaSim library
# -----------------
$(VLIB):
	mkdir -p $(@D)
	vlib $(VLIB)

# Directories
# -----------
$(TEST_DIR)/obj $(TEST_DIR)/dump $(TEST_DIR)/mem:
	mkdir -p $@
	
# Clean rule
# ----------
.PHONY: clean
clean:
	if [ -d $(VLIB) ]; then vdel -lib $(VLIB) -all; fi
	$(RM) -r $(TEST_DIR)/obj $(TEST_DIR)/dump $(TEST_DIR)/mem

.PHONY: clean-all
clean-all: | clean
	$(RM) -r $(BUILD_DIR)

.test:
	@echo $(VLOG_ARGS)
	@echo $(VLOG)