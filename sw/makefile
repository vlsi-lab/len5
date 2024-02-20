#############################
# ----- CONFIGURATION ----- #
#############################

# General configuration
MAKE			?= make
BUILD_DIR		?= build

# Target application
PROJECT			?= hello_world
LINKER 			?= linker/len5-sim.ld
SRCS 			:= $(wildcard applications/$(PROJECT)/*.c)
SRCS 			+= $(wildcard applications/$(PROJECT)/*.S)
OBJS 			:= $(filter %.o,\
				   $(patsubst %.c,$(BUILD_DIR)/%.o,$(SRCS))\
				   $(patsubst %.S,$(BUILD_DIR)/%.o,$(SRCS)))
INC_DIRS 		:= $(sort $(dir $(SRCS)))
INC_DIRS_GCC	:= $(addprefix -I ,$(INCLUDE_DIRS))

###  RISC-V C toolchain
# TODO: REMOVE -mstrict-align ONCE UNALIGNED ACCESS IS SUPPORTED
RISCV_EXE_PREFIX           	?= riscv64-unknown-elf
ISA_STRING					?= rv64i
ABI_STRING					?= lp64
COPT						?= -O0
CFLAGS			:= -march=$(ISA_STRING) \
				   -mabi=$(ABI_STRING) \
				   -mstrict-align \
				   -nostartfiles \
				   $(COPT) \
				   -Wall
LDFLAGS_PRE		:= -T $(LINKER) \
				   -static
LDFLAGS_POST	:= -Wl,-Map,$(BUILD_DIR)/main.map \
				   -Wl,--gc-sections \
				   -flto \
				   -ffunction-sections \
				   -fdata-sections \
				   -specs=nano.specs

# LEN5 software support
LIB_SRCS		:= $(wildcard device/crt/*.S) \
				   $(wildcard device/runtime/*.c device/runtime/*.S) \
				   $(wildcard device/base/**.c device/base/**.S)
LIB_INCS		:= $(wildcard device/base/*.h device/base/freestanding/*.h device/runtime/*.h)
INC_FOLDERS     += $(sort $(dir $(LIB_INCS)))
INC_FOLDERS_GCC += $(addprefix -I ,$(INC_FOLDERS))
LIB_OBJS		:= $(filter %.o,\
				   $(patsubst %.S,$(BUILD_DIR)/%.o,$(LIB_SRCS))\
				   $(patsubst %.s,$(BUILD_DIR)/%.o,$(LIB_SRCS))\
				   $(patsubst %.c,$(BUILD_DIR)/%.o,$(LIB_SRCS)))

#######################
# ----- TARGETS ----- #
#######################

# Software build
# --------------
# Application build
.PHONY: app
app: $(BUILD_DIR)/main.hex $(BUILD_DIR)/main.disasm

$(BUILD_DIR)/main.%: $(BUILD_DIR)/applications/$(PROJECT)/main.%
	cp $< $@

# ASCII .hex firmware
$(BUILD_DIR)/%.hex: $(BUILD_DIR)/%.elf
	$(RISCV_EXE_PREFIX)-objcopy -O verilog $< $@

# Disassembly
$(BUILD_DIR)/%.disasm: $(BUILD_DIR)/%.elf
	$(RISCV_EXE_PREFIX)-objdump -D $< > $@

# Stripped binary firmware
$(BUILD_DIR)/%.bin: $(BUILD_DIR)/%.elf
	$(RISCV_EXE_PREFIX)-objcopy -O binary $< $@

# Linked executable firmware
$(BUILD_DIR)/%.elf: $(OBJS) $(LIB_OBJS)
	$(RISCV_EXE_PREFIX)-gcc $(CFLAGS) $(LDFLAGS_PRE) $(INC_FOLDERS_GCC) $^ $(LDFLAGS_POST) -o $@

# Implicit compilation rules
$(BUILD_DIR)/%.o: ./%.c
	@mkdir -p $(@D)
	$(RISCV_EXE_PREFIX)-gcc $(CFLAGS) $(INC_FOLDERS_GCC) -c $< -o $@
$(BUILD_DIR)/%.o: ./%.S
	@mkdir -p $(@D)
	$(RISCV_EXE_PREFIX)-gcc $(CFLAGS) $(INC_FOLDERS_GCC) -c $< -o $@

# Utils
# -----
# Create new directories
%/:
	mkdir -p $@

# Print variables
.PHONY: .print
.print:
	@echo "RISCV:        $(RISCV)"
	@echo "PROJECT:      $(PROJECT)"
	@echo "SRCS          $(SRCS)"
	@echo "OBJS          $(OBJS)"
	@echo "LIB_SRCS:     $(LIB_SRCS)"
	@echo "LIB_OBJS:     $(LIB_OBJS)"
	@echo "LIB_INCS:     $(LIB_INCS)"
	@echo "INC_FOLDERS:  $(INC_FOLDERS)"
	@echo "CFLAGS:       $(CFLAGS)"
	@echo "LDFLAGS_PRE:  $(LDFLAGS_PRE)"
	@echo "LDFLAGS_POST: $(LDFLAGS_POST)"

# Clean-up
.PHONY: clean
clean:
	$(RM) -r $(BUILD_DIR)/*/*.elf
	$(RM) -r $(BUILD_DIR)/*/*.o
	$(RM) -r $(BUILD_DIR)/*/*.bin
	$(RM) -r $(BUILD_DIR)/*/*.hex
	$(RM) -r $(BUILD_DIR)/*/*.dis
	$(RM) -r $(BUILD_DIR)/*/*.map
	$(RM) -r $(BUILD_DIR)/*/*.dump
