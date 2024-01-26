####################
# ----- INFO ----- #
####################
# Makefile to generate the LEN5 processor files and build the design with fusesoc

#############################
# ----- CONFIGURATION ----- #
#############################

# General configuration
MAKE           	?= make
BUILD_DIR	   	?= $(realpath .)/build

# Get the absolute path
mkfile_path 	:= $(shell dirname "$(realpath $(firstword $(MAKEFILE_LIST)))")

# VARIABLES
# ---------
# Software build configuration
PROJECT  ?= hello_world

ifndef CONDA_DEFAULT_ENV
$(info USING VENV)
PYTHON  = $(PWD)/$(VENV)/python
else
$(info USING MINICONDA $(CONDA_DEFAULT_ENV))
PYTHON  := $(shell which python)
endif

#######################
# ----- TARGETS ----- #
#######################

# HDL source
# ----------
# Format code
.PHONY: format
format: | .check-fusesoc
	@echo "## Formatting RTL code..."
	fusesoc run --no-export --target format polito:len5:len5

# Static analysis
.PHONY: lint
lint: | .check-fusesoc
	@echo "## Running static analysis..."
	fusesoc run --no-export --target lint polito:len5:len5

# RTL simulation
# --------------
# QuestaSim
.PHONY: questasim-sim
questasim-sim: | .check-fusesoc
	@echo "## Running simulation with QuestaSim"
	$(FUSESOC) run --no-export --target=sim --tool=modelsim $(FUSESOC_FLAGS) --setup --build polito:len5:len5 2>&1 | tee builsim.log

# Verilator
# TODO: add verilator support to .core files

# Software
# --------
# Application from 'sw/applications'
.PHONY: app
app:
	@echo "## Building application '$(PROJECT)'"
	$(MAKE) -C sw app PROJECT=$(PROJECT) BUILD_DIR=$(BUILD_DIR)

# Simple test application
.PHONY: app-helloworld
app-helloworld:
	@echo "## Building helloworld application"
	$(MAKE) -C sw PROJECT=hello_world BUILD_DIR=$(BUILD_DIR)

# Compile example applicationa and run RTL simulation
.PHONY: app-helloworld-questasim
run-helloworld-questasim: questasim-sim app-helloworld | .check-fusesoc
	@echo "## Running helloworld application"
	cd ./build/vlsi_polito_len5_0/sim-modelsim; \
	make run PLUSARGS="c firmware=../../../sw/applications/hello_world.hex"; \
	cd ../../..;

# Utilities
# ---------
# Check if fusesoc is available
.PHONY: .check-fusesoc
.check-fusesoc:
	@if [ ! `which fusesoc` ]; then \
	printf -- "### ERROR: 'fusesoc' is not in PATH. Is the correct conda environment active?\n" >&2; \
	exit 1; fi

# Create new directories
%/:
	mkdir -p $@

# RTL format with Verible
.PHONY: format-verible
verible-format:
	scripts/format-verible;

# Clean-up
.PHONY: clean
clean: clean-app clean-sim

.PHONY: clean-sim
clean-sim:
	@rm -rf build

.PHONY: clean-app
clean-app:
	$(MAKE) -C sw clean