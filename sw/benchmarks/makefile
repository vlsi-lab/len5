#############################
# ----- CONFIGURATION ----- #
#############################

# Target application
SUITE			?= embench 
BENCHMARK 		?= crc32
LINKER 			?= ../linker/len5-sim.ld
BENCH_SRCS 			:= $(wildcard $(SUITE)/src/$(BENCHMARK)/*.c)
BENCH_SRCS 			+= $(wildcard $(SUITE)/src/$(BENCHMARK)/*.S)
BENCH_SRCS 			+= $(wildcard $(SUITE)/support/*.c)
BENCH_SRCS 			+= $(wildcard $(SUITE)/support/*.S)
ifeq ($(SUITE),  embench) # If embench suite, then include files are found in support dir
BENCH_SRCS 			+= $(wildcard $(SUITE)/support/*.c)
BENCH_SRCS 			+= $(wildcard $(SUITE)/support/*.S)
endif
BENCH_OBJS 			:= $(filter %.o,\
				   $(patsubst %.c,$(BUILD_DIR)/%.o,$(BENCH_SRCS))\
				   $(patsubst %.S,$(BUILD_DIR)/%.o,$(BENCH_SRCS)))

###  RISC-V C toolchain
# TODO: REMOVE -mstrict-align ONCE UNALIGNED ACCESS IS SUPPORTED
LDFLAGS_PRE		:= -T ../$(LINKER) \
				   -static

LDFLAGS_POST	+= -lm # This MUST BE put post the c files to enable math benchmarks

# LEN5 software support
LIB_SRCS		:= $(wildcard ../device/crt/*.S) \
				   $(wildcard ../device/runtime/*.c ../device/runtime/*.S) \
				   $(wildcard ../device/base/**.c ../device/base/**.S)
LIB_INCS		:= $(wildcard ../device/base/*.h ../device/base/freestanding/*.h ../device/runtime/*.h)

ifeq ($(SUITE),  embench) # If embench suite, then include files are found in support dir
LIB_INCS		+= $(wildcard ../benchmarks/$(SUITE)/support/*.h)
endif

ifeq ($(SUITE),  coremark) # If embench suite, then include files are found in support dir
LIB_INCS		+= $(wildcard ../benchmarks/$(SUITE)/src/*.h)
endif

INC_FOLDERS     += $(sort $(dir $(LIB_INCS)))
INC_FOLDERS_GCC += $(addprefix -I ,$(INC_FOLDERS))
LIB_OBJS		:= $(filter %.o,\
				   $(patsubst ../%.S,$(BUILD_DIR)/%.o,$(LIB_SRCS))\
				   $(patsubst ../%.s,$(BUILD_DIR)/%.o,$(LIB_SRCS))\
				   $(patsubst ../%.c,$(BUILD_DIR)/%.o,$(LIB_SRCS)))



#######################
# ----- TARGETS ----- #
#######################

# Software build
# --------------
# Benchmark build

.PHONY: embench
embench: $(BUILD_DIR)/main.hex $(BUILD_DIR)/main.disasm

.PHONY: coremark 
coremark: $(BUILD_DIR)/main.hex $(BUILD_DIR)/main.disasm

$(BUILD_DIR)/main.%: $(BUILD_DIR)/benchmarks/$(SUITE)/$(BENCHMARK)/main.%
	cp $< $@

# ASCII .hex firmware
$(BUILD_DIR)/main.hex: $(BUILD_DIR)/main.elf
	$(RISCV_EXE_PREFIX)-objcopy -O verilog $< $@

# Disassembly
$(BUILD_DIR)/main.disasm: $(BUILD_DIR)/main.elf
	$(RISCV_EXE_PREFIX)-objdump -D $< > $@

# Stripped binary firmware
$(BUILD_DIR)/%.bin: $(BUILD_DIR)/%.elf
	$(RISCV_EXE_PREFIX)-objcopy -O binary $< $@

# Linked executable firmware
$(BUILD_DIR)/main.elf: $(BENCH_OBJS) $(LIB_OBJS)
	$(RISCV_EXE_PREFIX)-gcc $(CFLAGS) $(LDFLAGS_PRE) $(INC_FOLDERS_GCC) $^ $(LDFLAGS_POST) -o $@

# Implicit compilation rules
$(BUILD_DIR)/%.o: ./%.c
	@mkdir -p $(@D)
	echo $(CFLAGS)
	$(RISCV_EXE_PREFIX)-gcc $(CFLAGS) $(INC_FOLDERS_GCC) -c $< -o $@
$(BUILD_DIR)/%.o: %.S
	@mkdir -p $(@D)
	$(RISCV_EXE_PREFIX)-gcc $(CFLAGS) $(INC_FOLDERS_GCC) -c $< -o $@

# Utils
# -----
# Create new directories
%/:
	mkdir -p $@