#############################
# ----- CONFIGURATION ----- #
#############################

# General configuration
MAKE			?= make
BUILD_DIR		?= ./build

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
RISCV_EXE_PREFIX           	?= riscv64-unknown-elf
ISA_STRING					?= rv64izicsr
ABI_STRING					?= lp64
CFLAGS			:= -march=$(ISA_STRING) \
				   -mabi=$(ABI_STRING) \
				   -mstrict-align \ # TODO: REMOVE WHEN UNALIGNED ACCESS IS SUPPORTED
				   -nostartfiles \
				   -O0 \
				   -g \
				   -Wall 
LDFLAGS			:= -T $(LINKER) \
				   -static \
				   -L $(RISCV)/$(RISCV_EXE_PREFIX)/lib \
				   -Wl,--gc-sections \
				   -lc \
				   -lm \
				   -lgcc \
				   -flto \
				   -ffunction-sections \
				   -fdata-sections \
				   -specs=nano.specs
ARFLAGS			:= rcus # s replaces ranlib

# GCC configuration
#LIB_CRT                    = $(wildcard src/crt0.S)
#LIB_CRT                    += $(wildcard src/irq.S)
#LIB_BASE                   = $(wildcard src/*.c)
#LIB_RUNTIME                =
#LIB_DRIVERS                += $(wildcard /*.c)

# LEN5 software support
LIB_SRCS		:= device/crt/crt0.S \
				   device/crt/vectors.S \
				   device/runtime/len5.c \
				   device/runtime/syscall.c \
				   device/base/memory.c
INC_FOLDERS     += $(sort $(dir $(LIB_SRCS)))
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

$(BUILD_DIR)/%: $(BUILD_DIR)/applications/$(PROJECT)/%
	ln -sr $< $@

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
	$(RISCV_EXE_PREFIX)-gcc $(CFLAGS) $(INC_FOLDERS_GCC) $(LDFLAGS) $^ -o $@

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
	@echo "RISCV:       $(RISCV)"
	@echo "PROJECT:     $(PROJECT)"
	@echo "SRCS         $(SRCS)"
	@echo "OBJS         $(OBJS)"
	@echo "LIB_SRCS:    $(LIB_SRCS)"
	@echo "LIB_OBJS:    $(LIB_OBJS)"
	@echo "INC_FOLDERS: $(INC_FOLDERS)"
	@echo "CFLAGS:      $(CFLAGS)"
	@echo "LDFLAGS:     $(LDFLAGS)"

# Clean-up
clean:
	$(RM) -r $(BUILD_DIR)/*/*.elf
	$(RM) -r $(BUILD_DIR)/*/*.o
	$(RM) -r $(BUILD_DIR)/*/*.bin
	$(RM) -r $(BUILD_DIR)/*/*.hex
	$(RM) -r $(BUILD_DIR)/*/*.dis
	$(RM) -r $(BUILD_DIR)/*/*.map
	$(RM) -r $(BUILD_DIR)/*/*.dump