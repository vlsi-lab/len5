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
HW_BUILD_DIR	:= $(BUILD_DIR)/hw
SW_BUILD_DIR    := $(BUILD_DIR)/sw
VWORK 			?= $(HW_BUILD_DIR)/len5

# LEN5 HDL files
PKG_SRCS 		:= 	$(ROOT)/include/len5_pkg.sv \
					$(ROOT)/include/csr_pkg.sv \
					$(ROOT)/include/fetch_pkg.sv \
					$(ROOT)/include/expipe_pkg.sv \
					$(ROOT)/include/memory_pkg.sv
# NOTE: currently compile non virtual memory source only
MODULES_SRCS 	:= 	$(shell find $(ROOT)/src/ -type f -name '*.sv' -not -path "$(ROOT)/src/**-vm/*" -not -path "$(ROOT)/src/**_vm.sv" -not -path "$(ROOT)/src/memory/*")
TB_SRCS 		:= 	$(ROOT)/tb/tb_with_l2cemu.sv \
					$(ROOT)/tb/tb_bare.sv \
					$(ROOT)/tb/memory/cache_L2_system_emulator.sv \
					$(ROOT)/tb/memory/memory_if.sv \
					$(ROOT)/tb/memory/memory_bare_emu.sv

# LEN5 test files
TEST_DIR 		:= $(ROOT)/test-files
TEST_SRCS		:= $(shell find $(TEST_DIR)/src/ -name '*.c' -or -name '*.s')
TESTS			:= $(addprefix tests/,$(basename $(notdir $(TEST_SRCS))))

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
VLOG			:= vlog -pedanticerrors -work $(VWORK) $(GLOBAL_OPT) $(UVM_OPT)
VLOG 			+= $(VLOG_ARGS) # from environment

# LEN5 software directory
SW_DIR			:= $(ROOT)/sw

###########################
# ----- BUILD RULES ----- #
###########################

# Aliases
# -------
.PHONY: all
all: hw sw
.PHONY: hw
hw: tb
.PHONY: sw
sw: test-files

# Hardware
# --------
# Packages
.PHONY: packages .check-vlog
packages: $(HW_BUILD_DIR)/pkg_list.f
$(HW_BUILD_DIR)/pkg_list.f: $(PKG_SRCS) | $(VWORK)
	@echo "## Compiling LEN5 packages..."
	@printf '%s\n' $? > $@
	$(VLOG) $(PKG_OPT) -F $@

# Source files
.PHONY: source-files .check-vlog
source-files: $(HW_BUILD_DIR)/src_list.f
$(HW_BUILD_DIR)/src_list.f: $(MODULES_SRCS) | $(HW_BUILD_DIR)/pkg_list.f
	@echo "## Compiling LEN5 source files..."
	@printf '%s\n' $? > $@
	$(VLOG) $(MODULE_OPT) -F $@

# Testbench
.PHONY: tb .check-vlog
tb: $(HW_BUILD_DIR)/tb_list.f
$(HW_BUILD_DIR)/tb_list.f: $(TB_SRCS) | $(HW_BUILD_DIR)/src_list.f
	@echo "## Compiling LEN5 testbench files..."
	@printf '%s\n' $? > $@
	$(VLOG) $(MODULE_OPT) -F $@

# Custom files
.PHONY: custom-src .check-vlog
custom-src: $(HW_BUILD_DIR)/$(CUSTOM_SRC_LIST) | $(HW_BUILD_DIR)/pkg_list.f
	@echo "## Compiling custom source files..."
	$(VLOG) $(MODULE_OPT) -F $<

# Check if vlog is available
.PHONY: .check-vlog
.check-vlog:
	@if [ ! `which vlog` ]; then \
	printf -- "### ERROR: 'vlog' is not in PATH. Did you run the initialization script?\n" >&2; \
	exit 1; fi

# QuestaSim library
$(VWORK): .check-vlog
	@echo "## Creating library '$@'..."
	mkdir -p $(@D)
	vlib $(VWORK)

# Software
# --------
# Test programs
.PHONY: test-files
test-files: liblen5
	@echo "## Compiling LEN5 test files"
	$(MAKE) -C $(TEST_DIR) all
.PHONY: $(TESTS)
$(TESTS):
	@echo "## Compiling test '$@'..."
	$(MAKE) -C $(TEST_DIR) $@

# LEN5 library with crt0, IRQ table, _write
.PHONY: liblen5
liblen5: 
	$(MAKE) -C $(SW_DIR)

# Directories
# -----------
$(BUILD_DIR) $(HW_BUILD_DIR):
	mkdir -p $@
	
# Clean rules
# -----------
.PHONY: clean
clean:
	if [ -d $(VWORK) ]; then vdel -lib $(VWORK) -all; fi
	$(RM) $(HW_BUILD_DIR)/*.f
	$(MAKE) -C $(SW_DIR) clean
	$(MAKE) -C $(TEST_DIR) clean

.PHONY: clean-all
clean-all:
	$(RM) -r $(BUILD_DIR)

.test:
	@echo "Packages:"
	@printf ' - %s\n' $(PKG_SRCS)
	@echo
	@echo "Source files:"
	@printf ' - %s\n' $(MODULES_SRCS)
