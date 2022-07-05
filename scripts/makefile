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
PKG_SRCS 		:= 	$(ROOT)/include/len5_pkg.sv \
					$(ROOT)/include/csr_pkg.sv \
					$(ROOT)/include/memory_pkg.sv \
					$(ROOT)/include/expipe_pkg.sv
MODULES_SRCS 	:= 	$(shell find $(ROOT)/src/ -type f -name '*.sv')
TB_SRCS 		:= 	$(ROOT)/tb/tb_with_l2cemu.sv \
					$(ROOT)/tb/memory/cache_L2_system_emulator.sv
# vlog options
GLOBAL_OPT		:= 	-svinputport=compat \
					-hazards \
					-vmake \
					+incdir+$(ROOT)/include \
					+incdir+$(ROOT)/tb/memory
UVM_OPT			:= +define+UVM_REPORT_DISABLE_FILE
PKG_OPT			:=
MODULE_OPT		:=
TB_OPT			:=

# SystemVerilog compiler
ifeq (, $(shell which vlog))
$(error 'vlog' is not in PATH. Did you run the initialization script?)
endif
VLOG			:= vlog -work $(VLIB) $(GLOBAL_OPT) $(UVM_OPT)
VLOG 			+= $(VLOG_ARGS) # from environment

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
packages: $(BUILD_DIR)/pkg_list.f
$(BUILD_DIR)/pkg_list.f: $(PKG_SRCS) | $(VLIB)
	@echo "## Compiling LEN5 packages..."
	@printf '%s\n' $? > $@
	$(VLOG) $(PKG_OPT) -F $@

# Source files
.PHONY: source-files
source-files: $(BUILD_DIR)/src_list.f
$(BUILD_DIR)/src_list.f: $(MODULES_SRCS) | $(BUILD_DIR)/pkg_list.f
	@echo "## Compiling LEN5 source files..."
	@printf '%s\n' $? > $@
	$(VLOG) $(MODULE_OPT) -F $@

# Testbench
.PHONY: tb
tb: $(BUILD_DIR)/tb_list.f $(TEST_MEM)
$(BUILD_DIR)/tb_list.f: $(TB_SRCS) | $(BUILD_DIR)/src_list.f
	@echo "## Compiling LEN5 testbench files..."
	@printf '%s\n' $? > $@
	$(VLOG) $(MODULE_OPT) -F $@

# Test memory files
.PHONY: test-files
test-files: $(TEST_MEM)
	@echo "## Compiling test files..."

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
	@echo "## Creating library '$@'..."
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
	$(RM) $(BUILD_DIR)/*.f

.PHONY: clean-all
clean-all: | clean
	$(RM) -r $(BUILD_DIR)

.test:
	@echo "Packages:"
	@printf ' - %s\n' $(PKG_SRCS)
	@echo
	@echo "Source files:"
	@printf ' - %s\n' $(MODULES_SRCS)