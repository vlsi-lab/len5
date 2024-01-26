MAKE                       = make

BUILD_DIR		?= ./build
LEN5_LIB 		:= $(BUILD_DIR)/lib/liblen5.a
# LEN5 software support
SW_SUPP_SRCS	:= src/crt0.S \
				   src/irq.S \
				   src/len5.c \
				   src/syscall.c
LD_SCRIPT		:= len5-sim.ld

###  RISC-V C compiler
# riscv toolchain install path
RISCV                      	?= ~/.riscv
RISCV_EXE_PREFIX           	?= riscv64-unknown-elf-
ISA_STRING					?= rv64i
ABI_STRING					?= lp64
CFLAGS			:= 	-march=$(ISA_STRING) \
					-mabi=$(ABI_STRING) \
					-mcmodel=medlow \
					-ffreestanding \
					-ffunction-sections \
					-O1 \
					-Wall
LDFLAGS			:= -nostartfiles \
				   -static \
				   -L$(BUILD_DIR)/lib \
				   -Wl,--gc-sections \
				   -Wl,--whole-archive \
				   -llen5
AR 				:= $(RISCV_EXE_PREFIX)ar
ARFLAGS			:= rcus # s replaces ranlib

# GCC configuration
INC_FOLDERS_GCC            = $(addprefix -I ,$(INC_FOLDERS))
#LIB_CRT                    = $(wildcard src/crt0.S)
#LIB_CRT                    += $(wildcard src/irq.S)
#LIB_BASE                   = $(wildcard src/*.c)
#LIB_RUNTIME                = 
#LIB_DRIVERS                += $(wildcard /*.c)
INC_FOLDERS                += $(sort $(dir $(wildcard include/)))
LIB_OBJS		:= $(filter %.o,\
				   $(patsubst $(SW_DIR)/src/%.S,$(BUILD_DIR)/obj/%.o,$(LIB_SRCS))\
				   $(patsubst $(SW_DIR)/src/%.s,$(BUILD_DIR)/obj/%.o,$(LIB_SRCS))\
				   $(patsubst $(SW_DIR)/src/%.c,$(BUILD_DIR)/obj/%.o,$(LIB_SRCS)))


# Rules to generate bin (loadable by simulators) from elf
%.bin : %.elf
	$(RISCV_EXE_PREFIX)objcopy -O binary $< $@

%.hex : %.elf
	$(RISCV_EXE_PREFIX)objcopy -O verilog $< $@

%.elf: %.o $(LEN5_LIB) 
	$(RISCV_EXE_PREFIX)gcc $(CFLAGS) $(INC_FOLDERS_GCC) -T $(LD_SCRIPT) $(LDFLAGS) $< -o $@

# Software support files (crt0, _write, headers)
# Executed when the support files changes
$(LEN5_LIB): $(LIB_OBJS) | $(BUILD_DIR)/lib/
	$(AR) $(ARFLAGS) $@ $+

%/.o: %.c 
	$(RISCV_EXE_PREFIX)gcc $(CFLAGS) $(INC_FOLDERS_GCC) -c $< -o $@

# Directories
# -----------
%/:
	mkdir -p $@
	
clean:
	rm -rf $(BUILD_DIR)/*/*.elf \
	rm -rf $(BUILD_DIR)/*/*.o \
	rm -rf $(BUILD_DIR)/*/*.bin \
	rm -rf $(BUILD_DIR)/*/*.hex \
	rm -rf $(BUILD_DIR)/*/*.dis \
	rm -rf $(BUILD_DIR)/*/*.map \
	rm -rf $(BUILD_DIR)/*/*.dump \