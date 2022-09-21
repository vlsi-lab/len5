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
MODULES_INCS	:= 	$(shell find $(ROOT)/src/ $(ROOT)/include/ -type f -name "*.svh")
TB_SRCS 		:= 	$(ROOT)/tb/tb_with_l2cemu.sv \
					$(ROOT)/tb/tb_bare.sv \
					$(ROOT)/tb/memory/cache_L2_system_emulator.sv \
					$(ROOT)/tb/memory/memory_if.sv \
					$(ROOT)/tb/memory/memory_bare_emu.sv
TB_INCS			:= 	$(shell find $(ROOT)/src/ $(ROOT)/include/ $(ROOT)/tb/ -type f -name "*.svh")
ifdef CUSTOM_SRC_DIR
CUSTOM_PKGS		?= 	$(shell grep --include=\*.sv -rlE "^package \w+;" $(CUSTOM_SRC_DIR))
CUSTOM_SRCS 	?=	$(shell find $(CUSTOM_SRC_DIR) -type f -name '*.sv')
endif

# LEN5 test files
SW_DIR			:= $(ROOT)/sw
TEST_DIR 		:= $(SW_DIR)/test-programs
TEST_SRCS		:= $(shell find $(TEST_DIR)/src -name '*.c' -or -name '*.s')
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
.PHONY: packages
packages: $(HW_BUILD_DIR)/.cache/.pkg_done
$(HW_BUILD_DIR)/.cache/.pkg_done: $(HW_BUILD_DIR)/.cache/pkg_list.f | .check-vlog
	@echo "## Compiling LEN5 files..."
	$(VLOG) $(PKG_OPT) -F $<
	touch $@
$(HW_BUILD_DIR)/.cache/pkg_list.f: $(PKG_SRCS) | $(HW_BUILD_DIR)/.cache
	@echo "## Assembling list of updated LEN5 packages..."
	@printf '%s\n' $? > $@

# Modules
.PHONY: modules
modules: $(HW_BUILD_DIR)/.cache/.mod_done
$(HW_BUILD_DIR)/.cache/.mod_done : $(HW_BUILD_DIR)/.cache/src_list.f $(MODULES_INCS) $(HW_BUILD_DIR)/.cache/.pkg_done | .check-vlog
	@echo "## Compiling LEN5 modules..."
	$(VLOG) $(MODULE_OPT) -F $<
	touch $@
$(HW_BUILD_DIR)/.cache/src_list.f: $(MODULES_SRCS) | $(HW_BUILD_DIR)/.cache
	@echo "## Assembling list of updated LEN5 modules..."
	@printf '%s\n' $? > $@

# Testbench
.PHONY: tb
tb: $(HW_BUILD_DIR)/.cache/.tb_done
$(HW_BUILD_DIR)/.cache/.tb_done: $(HW_BUILD_DIR)/.cache/tb_list.f $(MODULES_INCS) $(TB_INCS) $(HW_BUILD_DIR)/.cache/.mod_done | .check-vlog
	@echo "## Compiling LEN5 testbench..."
	$(VLOG) $(MODULE_OPT) -F $<
	touch $@
$(HW_BUILD_DIR)/.cache/tb_list.f: $(TB_SRCS) | $(HW_BUILD_DIR)/.cache
	@echo "## Assembling list of updated LEN5 testbench files..."
	@printf '%s\n' $? > $@

# Custom files
.PHONY: custom-src
custom-src: $(HW_BUILD_DIR)/.cache/.custom_done 
$(HW_BUILD_DIR)/.cache/.custom_done: $(HW_BUILD_DIR)/.cache/custom_list.f $(HW_BUILD_DIR)/.cache/.pkg_done | .check-vlog
	@echo "## Compiling custom modules..."
	$(VLOG) $(MODULE_OPT) -F $<
	touch $@
$(HW_BUILD_DIR)/.cache/custom_list.f: $(CUSTOM_PKGS) $(CUSTOM_SRCS) | $(HW_BUILD_DIR)/.cache
	@echo "Assembling list of updated custom modules..."
	@printf '%s\n' $? > $@

# QuestaSim library
$(VWORK): | .check-vlog
	@echo "## Creating library '$@'..."
	mkdir -p $(@D)
	vlib $(VWORK)

# Check if vlog is available
.PHONY: .check-vlog
.check-vlog:
	@if [ ! `which vlog` ]; then \
	printf -- "### ERROR: 'vlog' is not in PATH. Did you run the initialization script?\n" >&2; \
	exit 1; fi

# Software
# --------
# Test programs
.PHONY: test-files
test-files:
	@echo "## Compiling LEN5 test files"
	$(MAKE) -C $(SW_DIR) all
.PHONY: $(TESTS)
$(TESTS):
	@echo "## Compiling test '$@'..."
	$(MAKE) -C $(SW_DIR) $@

.PHONY: print-tests
print-tests:
	@printf -- "Available tests:\n"
	@printf -- "> %s\n" $(TESTS:tests/%=%)

# Directories
# -----------
$(BUILD_DIR) $(HW_BUILD_DIR) $(HW_BUILD_DIR)/.cache:
	mkdir -p $@
	
# Clean rules
# -----------
.PHONY: clean
clean:
	if [ -d $(VWORK) ]; then vdel -lib $(VWORK) -all; fi
	$(RM) -r $(HW_BUILD_DIR)
	$(MAKE) -C $(SW_DIR) clean

.PHONY: clean-all
clean-all:
	$(RM) -r $(BUILD_DIR)

# Debug
.test:
	@echo $(ROOT)
	@echo $(TEST_DIR)
.list:
	@echo "Packages:"
	@printf ' - %s\n' $(PKG_SRCS)
	@echo
	@echo "Source files:"
	@printf ' - %s\n' $(MODULES_SRCS)
	@echo "Test programs:"
	@printf ' - %s\n' $(TEST_SRCS)
