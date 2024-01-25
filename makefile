# Copyright PoliTO contributors.
####################
# ----- INFO ----- #
####################
# Makefile to generate the LEN5 processor files and build the design with fusesoc

MAKE             = make

# Get the absolute path
mkfile_path := $(shell dirname "$(realpath $(firstword $(MAKEFILE_LIST)))")

# VARIABLES
# ---------

# Target options are 'sim' (default) and 'synth'
TARGET   ?= sim

# Compiler option is 'gcc' (default)
COMPILER = gcc

# Compiler prefix options are 'riscv64-unknown-' (default)
COMPILER_PREFIX ?= riscv64-unknown-

ifndef CONDA_DEFAULT_ENV
$(info USING VENV)
FUSESOC = $(PWD)/$(VENV)/fusesoc
PYTHON  = $(PWD)/$(VENV)/python
else
$(info USING MINICONDA $(CONDA_DEFAULT_ENV))
FUSESOC := $(shell which fusesoc)
PYTHON  := $(shell which python)
endif

# Simulation
questasim-sim: 
	@echo "## Running simulation with QuestaSim"
	$(FUSESOC) --cores-root . run --no-export --target=sim --tool=modelsim $(FUSESOC_FLAGS) --setup --build vlsi:polito:len5_top | tee builsim.log	

app-helloworld:
	@echo "## Building helloworld application"
	$(MAKE) -C len5-software applications/hello_world/hello_world.hex  TARGET=$(TARGET)

run-helloworld-questasim: questasim-sim app-helloworld
	@echo "## Running helloworld application"
	cd ./build/vlsi_polito_len5_top_0/sim-modelsim; \
	make run PLUSARGS="c firmware=../../../len5-software/applications/hello_world.hex"; \
	cd ../../..;

########################################################################

# Runs verible formating
verible:
	scripts/format-verible;

clean: clean-app clean-sim

clean-sim:
	@rm -rf build

clean-app:
	$(MAKE) -C len5-software clean