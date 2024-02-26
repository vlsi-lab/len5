#############################
# ----- CONFIGURATION ----- #
#############################

BUILD_DIR	   	?= $(realpath .)/build

# Default parameters
LOG_LEVEL		?= LOG_NORMAL
MAX_CYCLES		?= 1000000

#######################
# ----- TARGETS ----- #
#######################

# Default target
.PHONY: all
all: verilator-sim

# Build Verilator model
# Re-run every time the necessary files (.core, RTL, CPP) change
.PHONY: verilator-build
verilator-build: $(BUILD_DIR)/
	@echo "## Building simulation model with Verilator..."
	fusesoc --cores-root ../../../ run --no-export --target sim --tool verilator --build $(FUSESOC_FLAGS) polito:len5:alu-tb

# Build and run Verilator simulation
.PHONY: verilator-sim
verilator-sim: | verilator-build
	fusesoc --cores-root ../../../ run --no-export --target sim --tool verilator --run $(FUSESOC_FLAGS) polito:len5:alu-tb \
		--log_level=$(LOG_LEVEL) \
		--max_cycles=$(MAX_CYCLES)

# Run Verilator simulation
.PHONY: verilator-run
verilator-run:
	fusesoc --cores-root ../../../ run --no-export --target sim --tool verilator --run $(FUSESOC_FLAGS) polito:len5:alu-tb \
		--log_level=$(LOG_LEVEL) \
		--max_cycles=$(MAX_CYCLES)

# Open dumped waveform with GTKWave
.PHONY: verilator-waves
verilator-waves: $(BUILD_DIR)/sim-common/waves.fst
	gtkwave -a alu-waves.gtkw $<

# Create new directories
%/:
	mkdir -p $@

.PHONY: clean
clean:
	@rm -rf build