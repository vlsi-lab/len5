####################
# ----- INFO ----- #
####################
# Compile test files

# Variables
# ---------
# Paths
ROOT 			:= ..
BUILD_DIR		?= $(ROOT)/build
SW_BUILD_DIR	:= $(BUILD_DIR)/sw
TEST_BUILD_DIR	:= $(SW_BUILD_DIR)/tests
TEST_DIR 		:= .
TEST_SRCS		:= $(shell find $(TEST_DIR)/src/ -name '*.c' -or -name '*.s')
TESTS			:= $(addprefix tests/,$(basename $(notdir $(TEST_SRCS))))
SW_DIR 			:= $(ROOT)/sw
LINK_SCRIPT		:= $(SW_BUILD_DIR)/len5-sim.ld

# RISC-V C compiler
CROSS_COMPILE 	?= riscv64-unknown-elf-
ISA_STRING		?= rv64i
ABI_STRING		?= lp64
CC 				:= $(CROSS_COMPILE)gcc
CFLAGS			:= -march=$(ISA_STRING) \
				   -mabi=$(ABI_STRING) \
				   -ffreestanding
CUSTOM_SRCS		:= $(SW_DIR)/src/crt0.S \
				   $(SW_DIR)/src/irq.S \
				   $(SW_DIR)/src/write.c
LDFLAGS			:= -T $(LINK_SCRIPT) \
				   -nostartfiles \
				   -static \
				   -Wl,--gc-sections
CINC			:= -I$(SW_BUILD_DIR)/include
AS 				:= $(CROSS_COMPILE)as
ASFLAGS			:= $(CFLAGS)
OBJDUMP			:= $(CROSS_COMPILE)objdump
OBJCOPY			:= $(CROSS_COMPILE)objcopy

###########################
# ----- BUILD RULES ----- #
###########################

# Software tests
# --------------
.PHONY: all
all: $(TESTS)
.PHONY: $(TESTS)
$(TESTS): tests/%: $(TEST_BUILD_DIR)/mem/%.mem $(TEST_BUILD_DIR)/dis/%.dis

# Implicit rules
.PRECIOUS: $(TEST_BUILD_DIR)/obj/%.o $(TEST_BUILD_DIR)/dis/%.dis $(TEST_BUILD_DIR)/bin/%
$(TEST_BUILD_DIR)/mem/%.mem: $(TEST_BUILD_DIR)/bin/% | $(TEST_BUILD_DIR)/mem
	$(OBJCOPY) -O binary $< $@
$(TEST_BUILD_DIR)/dis/%.dis: $(TEST_BUILD_DIR)/bin/% | $(TEST_BUILD_DIR)/dis
	$(OBJDUMP) -D $< > $@
$(TEST_BUILD_DIR)/bin/%: $(TEST_BUILD_DIR)/obj/%.o liblen5 | $(TEST_BUILD_DIR)/bin
	$(CC) $(CFLAGS) $(CINC) $(LDFLAGS) $(CUSTOM_SRCS) $< -o $@
$(TEST_BUILD_DIR)/obj/%.o: $(TEST_DIR)/src/%.c sw-support | $(TEST_BUILD_DIR)/obj
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@
$(TEST_BUILD_DIR)/obj/%.o: $(TEST_DIR)/src/%.S sw-support | $(TEST_BUILD_DIR)/obj
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@
$(TEST_BUILD_DIR)/obj/%.o: $(TEST_DIR)/src/%.s sw-support | $(TEST_BUILD_DIR)/obj
	$(CC) $(CFLAGS) $(CINC) -c $< -o $@

# LEN5 library and software support files
sw-support liblen5:
	$(MAKE) -C $(SW_DIR) $@

# Directories
# -----------
$(TEST_BUILD_DIR) $(TEST_BUILD_DIR)/obj $(TEST_BUILD_DIR)/bin $(TEST_BUILD_DIR)/dis $(TEST_BUILD_DIR)/mem:
	mkdir -p $@

# Clean rules
# -----------
.PHONY: clean
clean:
	$(RM) -r $(SW_BUILD_DIR)

.test:
	@echo $(TEST_SRCS)
	@echo $(TEST_OBJS)
	@echo $(TESTS)