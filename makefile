####################
# ----- INFO ----- #
####################
# Compile LEN5 RTL source files

# VARIABLES
# ---------

# Set Bash as default shell ('source' allows passing options to sourced scrips)
SHELL			:= /bin/bash

# Paths
ROOT 			:= $(realpath .)
BUILD_DIR 		?= $(ROOT)/build
HW_BUILD_DIR	?= $(BUILD_DIR)/hw
SW_BUILD_DIR    ?= $(BUILD_DIR)/sw
VLIB 			?= $(HW_BUILD_DIR)/len5

# LEN5 test files
TEST_DIR 		:= $(ROOT)/test-files
TEST_SRCS		:= $(shell find $(TEST_DIR)/src/ -name '*.c' -or -name '*.s')
TESTS			:= $(addprefix tests/,$(basename $(notdir $(TEST_SRCS))))

# LEN5 HDL files
PKG_SRCS 		:= 	$(ROOT)/include/len5_pkg.sv \
					$(ROOT)/include/csr_pkg.sv \
					$(ROOT)/include/fetch_pkg.sv \
					$(ROOT)/include/expipe_pkg.sv \
					$(ROOT)/include/memory_pkg.sv
# NOTE: currently compile non virtual memory source only
MODULES_SRCS 	:= 	$(shell find $(ROOT)/src/ -type f -name '*.sv' -not -path "$(ROOT)/src/**-vm/*" -not -path "$(ROOT)/src/**_vm.sv")
TB_SRCS 		:= 	$(ROOT)/tb/tb_with_l2cemu.sv \
					$(ROOT)/tb/tb_bare.sv \
					$(ROOT)/tb/memory/cache_L2_system_emulator.sv \
					$(ROOT)/tb/memory/memory_if.sv \
					$(ROOT)/tb/memory/memory_bare_emu.sv

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

# LEN5 software directory
SW_DIR			:= $(ROOT)/sw

###########################
# ----- BUILD RULES ----- #
###########################

# Files
# -----

.PHONY: all
all: tb test-files

# Packages
.PHONY: packages
packages: $(HW_BUILD_DIR)/pkg_list.f
$(HW_BUILD_DIR)/pkg_list.f: $(PKG_SRCS) | $(VLIB)
	@echo "## Compiling LEN5 packages..."
	@printf '%s\n' $? > $@
	$(VLOG) $(PKG_OPT) -F $@

# Source files
.PHONY: source-files
source-files: $(HW_BUILD_DIR)/src_list.f
$(HW_BUILD_DIR)/src_list.f: $(MODULES_SRCS) | $(HW_BUILD_DIR)/pkg_list.f
	@echo "## Compiling LEN5 source files..."
	@printf '%s\n' $? > $@
	$(VLOG) $(MODULE_OPT) -F $@

# Testbench
.PHONY: tb
tb: $(HW_BUILD_DIR)/tb_list.f $(TEST_MEM)
$(HW_BUILD_DIR)/tb_list.f: $(TB_SRCS) | $(HW_BUILD_DIR)/src_list.f
	@echo "## Compiling LEN5 testbench files..."
	@printf '%s\n' $? > $@
	$(VLOG) $(MODULE_OPT) -F $@

# Custom files
.PHONY: custom-src
custom-src: $(HW_BUILD_DIR)/$(CUSTOM_SRC_LIST) | $(HW_BUILD_DIR)/pkg_list.f
	@echo "## Compiling custom source files..."
	$(VLOG) $(MODULE_OPT) -F $<

# QuestaSim library
# -----------------
$(VLIB):
	@echo "## Creating library '$@'..."
	mkdir -p $(@D)
	vlib $(VLIB)

# Test files
# ----------
.PHONY: test-files
test-files:
	@echo "## Compiling LEN5 test files"
	$(MAKE) -C $(TEST_DIR) all
.PHONY: $(TESTS)
$(TESTS):
	$(MAKE) -C $(TEST_DIR) $@

# .PRECIOUS: $(TEST_DIR)/objdump/%.objdump $(TEST_DIR)/obj/%.o
# $(TEST_DIR)/mem/%.txt: $(TEST_DIR)/objdump/%.objdump | $(TEST_DIR)/mem
# 	awk '/[ ]+[0-9a-f]+:\t[0-9a-f]{8}/' $< | awk -f $(AWK_FORMAT) > $@
# $(TEST_DIR)/objdump/%.objdump: $(TEST_DIR)/obj/%.o | $(TEST_DIR)/objdump
# 	$(OBJDUMP) -M numeric -M no-aliases -d -j .text $< > $@
# $(TEST_DIR)/obj/%.o: $(TEST_DIR)/src/%.c | $(TEST_DIR)/obj
# 	$(CC) $(CFLAGS) $(CINC) -c $< -o $@
# $(TEST_DIR)/obj/%.o: $(TEST_DIR)/src/%.s | $(TEST_DIR)/obj
# 	$(AS) $(ASFLAGS) $(CINC) -c $< -o $@

# Libraries
# ---------
# Write dummy library (redefines _write from Newlib)
.PHONY: liblen5
liblen5: 
	$(MAKE) -C $(SW_DIR) liblen5

# Directories
# -----------
$(BUILD_DIR) $(HW_BUILD_DIR):
	mkdir -p $@
	
# Clean rule
# ----------
.PHONY: clean
clean:
	if [ -d $(VLIB) ]; then vdel -lib $(VLIB) -all; fi
	$(RM) $(HW_BUILD_DIR)/*.f
	$(MAKE) -C $(SW_DIR) clean
	$(MAKE) -C $(TEST_DIR) clean

.PHONY: clean-all
clean-all: | clean
	$(RM) -r $(BUILD_DIR)

.test:
	@echo "Packages:"
	@printf ' - %s\n' $(PKG_SRCS)
	@echo
	@echo "Source files:"
	@printf ' - %s\n' $(MODULES_SRCS)
