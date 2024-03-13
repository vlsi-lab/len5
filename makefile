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

# Software build configuration
PROJECT  		?= hello_world
SUITE   		?= embench
BENCHMARK 		?= crc32
LINKER   		?= $(realpath sw/linker/len5-sim.ld)
COPT   	 		?= -O2

# RTL simulation
FIRMWARE		?= $(BUILD_DIR)/main.hex
MAX_CYCLES		?= 100000
LOG_LEVEL		?= LOG_MEDIUM
DUMP_TRACE		?= true

# Regression tests
TEST_DIRS		:= $(wildcard sw/applications/*/)
TESTS			:= $(patsubst sw/applications/%/,%,$(TEST_DIRS))
TESTS_EXCLUDE	:= timer alu_mult alu_div #TODO fix
TESTS			:= $(filter-out $(TESTS_EXCLUDE),$(TESTS))

# VARIABLES
# ---------
# RTL simulation files
SIM_CORE_FILES 	:= $(shell find . -type f -name "*.core")
SIM_HDL_FILES 	:= $(shell find rtl -type f -name "*.v" -o -name "*.sv" -o -name "*.svh")
SIM_HDL_FILES 	+= $(shell find tb -type f -name "*.v" -o -name "*.sv" -o -name "*.svh")
SIM_CPP_FILES	:= $(shell find tb/verilator -type f -name "*.cpp" -o -name "*.hh")

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
# Build Verilator model
# Re-run every time the necessary files (.core, RTL, CPP) change
.PHONY: verilator-build
verilator-build: $(BUILD_DIR)/.verilator.lock
$(BUILD_DIR)/.verilator.lock: $(SIM_CORE_FILES) $(SIM_HDL_FILES) $(SIM_CPP_FILES) | .check-fusesoc $(BUILD_DIR)/
	@echo "## Building simulation model with Verilator..."
	fusesoc run --no-export --target sim --tool verilator $(FUSESOC_FLAGS) --build polito:len5:len5
	touch $@

# Run Verilator simulation
.PHONY: verilator-sim
verilator-sim: $(BUILD_DIR)/.verilator.lock $(BUILD_DIR)/main.hex | .check-fusesoc
	fusesoc run --no-export --target sim --tool verilator --run $(FUSESOC_FLAGS) polito:len5:len5 \
		--log_level=$(LOG_LEVEL) \
		--firmware=$(FIRMWARE) \
		--max_cycles=$(MAX_CYCLES) \
		--dump_trace=$(DUMP_TRACE) \
		$(FUSESOC_ARGS)

.PHONY: verilator-opt
verilator-opt: $(BUILD_DIR)/.verilator.lock $(BUILD_DIR)/main.hex | .check-fusesoc
	fusesoc run --no-export --target sim --tool verilator --run $(FUSESOC_FLAGS) polito:len5:len5 \
		--log_level=$(LOG_LEVEL) \
		--firmware=$(FIRMWARE) \
		--max_cycles=$(MAX_CYCLES) \
		--dump_waves=false \
		$(FUSESOC_ARGS)

$(BUILD_DIR)/sim-common/sim-trace.log: $(BUILD_DIR)/.verilator.lock $(BUILD_DIR)/main.hex
	@echo "## Running simulation with Verilator..."
	fusesoc run --no-export --target sim --tool verilator --run $(FUSESOC_FLAGS) polito:len5:len5 \
		--log_level=$(LOG_LEVEL) \
		--firmware=$(FIRMWARE) \
		--max_cycles=$(MAX_CYCLES) \
		--dump_trace=true \
		--dump_waves=$(DUMP_WAVES) \
		$(FUSESOC_ARGS)

# Open dumped waveform with GTKWave
.PHONY: verilator-waves
verilator-waves: $(BUILD_DIR)/sim-common/waves.fst | .check-gtkwave
	gtkwave -a tb/misc/verilator-waves.gtkw $<

# QuestaSim
.PHONY: questasim-sim
questasim-sim: | app .check-fusesoc $(BUILD_DIR)/
	@echo "## Running simulation with QuestaSim..."
	fusesoc run --no-export --target sim --tool modelsim $(FUSESOC_FLAGS) --build polito:len5:len5 2>&1 | tee build/build.log
	
# Software
# --------
# Application from 'sw/applications'
# NOTE: the -B option to make forces recompilation everytime, which is needed since PROJECT is user-defined
# The SPIKE_CHECK flag disables CSR instructions, since values differs between Spike and Verilator simulation 

.PHONY: app app-spike
app: | $(BUILD_DIR)/
	@echo "## Building application '$(PROJECT)'"
	$(MAKE) -BC sw app PROJECT=$(PROJECT) BUILD_DIR=$(BUILD_DIR) COPT=$(COPT)

$(BUILD_DIR)/spike/main.elf: app-spike
app-spike: | $(BUILD_DIR)/spike/
	@echo "## Building application '$(PROJECT)' with support for Spike"
	$(MAKE) -BC sw app PROJECT=$(PROJECT) BUILD_DIR=$(BUILD_DIR)/spike COPT=$(COPT) CDEFS=-DSPIKE_CHECK

.PHONY: benchmark benchmark-spike
benchmark:
	@echo "## Building suite $(SUITE) benchmark $(BENCHMARK)"
	$(MAKE) -BC sw benchmark SUITE=$(SUITE) BUILD_DIR=$(BUILD_DIR) BENCHMARK=$(BENCHMARK)

benchmark-spike: | $(BUILD_DIR)/spike/
	@echo "## Building suite $(SUITE) benchmark $(BENCHMARK)"
	$(MAKE) -BC sw benchmark SUITE=$(SUITE) BUILD_DIR=$(BUILD_DIR)/spike BENCHMARK=$(BENCHMARK) CDEFS=-DSPIKE_CHECK

.PHONY: run-benchmarks
run-benchmarks: 
	@echo "## Running suite $(SUITE)"
	python3 scripts/benchmarks.py -s $(SUITE) -O=2 -P=1000
	rm -rf build_*

# Simple test application
.PHONY: app-helloworld
app-helloworld:
	@echo "## Building helloworld application"
	$(MAKE) -BC sw PROJECT=hello_world BUILD_DIR=$(BUILD_DIR)

# Compile example applicationa and run RTL simulation
.PHONY: app-helloworld-questasim
run-helloworld-questasim: questasim-sim app-helloworld | .check-fusesoc
	@echo "## Running helloworld application"
	cd $(BUILD_DIR)/vlsi_polito_len5_0/sim-modelsim; \
	make run PLUSARGS="c firmware=../../../sw/applications/hello_world.hex"; \
	cd ../../..;

# Simulate the current application on Spike, in interactive mode (debug)
.PHONY: spike-sim
spike-sim: $(BUILD_DIR)/spike/main.elf
	@echo "## Running simulation with Spike..."
	spike -m0xf000:0x100000,0x20000000:0x1000 -d $<

# Simulate the current application on Spike in silent mode and generate the instruction execution trace
.PHONY: spike-trace
spike-trace: $(BUILD_DIR)/sim-common/spike-trace.log
$(BUILD_DIR)/sim-common/spike-trace.log: $(BUILD_DIR)/spike/main.elf | $(BUILD_DIR)/sim-common/
	@echo "## Running simulation with Spike..."
	spike --log-commits --log=$@ -l -m0xf000:0x100000,0x20000000:0x1000 $<

# Compare the execution traces from Spike and the Verilator simulation
.PHONY: spike-check
spike-check: $(BUILD_DIR)/.verilator.lock | $(BUILD_DIR)/sim-common/ .check-fusesoc
	@echo "## Launching Verilator simulation..."
	fusesoc run --no-export --target sim --tool verilator --run $(FUSESOC_FLAGS) polito:len5:len5 \
		--log_level=$(LOG_LEVEL) \
		--firmware=$(BUILD_DIR)/spike/main.hex \
		--max_cycles=$(MAX_CYCLES) \
		--dump_waves=false \
		--dump_trace=true \
		$(FUSESOC_ARGS)
	@echo "## Running Spike simulation..."
	spike --log-commits --log=$(BUILD_DIR)/sim-common/spike-trace.log -l -m0xf000:0x100000,0x20000000:0x1000 $(BUILD_DIR)/spike/main.elf
	@echo "## Comparing Spike and Verilator traces..."
	scripts/sim/cmp-trace.sh $(BUILD_DIR)/sim-common/sim-trace.log $(BUILD_DIR)/sim-common/spike-trace.log

# Check that nothing is broken
# ----------------------------
.PHONE: check
check: | check-alu .check-fusesoc
	@echo "### Executing regression tests..."
	@echo " ## Checking RTL..."
	fusesoc run --no-export --target format polito:len5:len5
	fusesoc run --no-export --target lint polito:len5:len5
	@echo " ## Simulating test applications..."
	$(foreach T, $(TESTS), eval $(MAKE) spike-check PROJECT=$(T) COPT=-O0 || exit 1;)
	$(foreach T, $(TESTS), eval $(MAKE) spike-check PROJECT=$(T) COPT=-O1 || exit 1;)
	$(foreach T, $(TESTS), eval $(MAKE) spike-check PROJECT=$(T) COPT=-O2 || exit 1;)
	@echo "\e[1;32m### SUCCESS: all checks passed!\e[0m"

.PHONY: check-alu
check-alu: | .check-fusesoc
	@echo "## Checking ALU RTL..."
	fusesoc run --no-export --target sim --tool verilator polito:len5:alu-tb \
		--log_level=LOG_LOW \
		--dump_waves=false \
		--max_cycles=1000000

# Utilities
# ---------
# Check if fusesoc is available
.PHONY: .check-fusesoc
.check-fusesoc:
	@if [ ! `which fusesoc` ]; then \
	printf -- "### ERROR: 'fusesoc' is not in PATH. Is the correct conda environment active?\n" >&2; \
	exit 1; fi

# Check if GTKWave is available
.PHONY: .check-gtkwave
.check-gtkwave:
	@if [ ! `which gtkwave` ]; then \
	printf -- "### ERROR: 'gtkwave' is not in PATH. Is the correct conda environment active?\n" >&2; \
	exit 1; fi

# Run plotting scripts
.PHONY: charts
charts: w/benchmarks/embench/output/benchmarks.csv scripts/xheep_resultsO2.csv
	mkdir -p $(BUILD_DIR)/charts
	python3 scripts/ipc_charts.py --len5_report_file=sw/benchmarks/embench/output/backup_bench.csv --xheep_report_file=scripts/xheep_resultsO2.csv --chart_file=$(BUILD_DIR)/charts/ipc_chart.png

# Create new directories
%/:
	mkdir -p $@

# Clean-up
.PHONY: clean
clean: clean-app clean-sim

.PHONY: clean-sim
clean-sim:
	@rm -rf $(BUILD_DIR)

.PHONY: clean-app
clean-app:
	$(MAKE) -C sw clean

.PHONY: .print
.print:
	@echo "SIM_HDL_FILES: $(SIM_HDL_FILES)"
	@echo "SIM_CPP_FILES: $(SIM_CPP_FILES)"
	@echo "TESTS: $(TESTS)"

# Export variables for software linker script
# -------------------------------------------
export BUILD_DIR
export PROJECT
export LINKER
export COPT
