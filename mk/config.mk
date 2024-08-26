# SPDX-License-Identifier: Apache-2.0
ifndef _CONFIG
_CONFIG :=

SRCDIR := $(CURDIR)

##############
# GCC config #
##############
CROSS_PREFIX ?= 
CC := $(CROSS_PREFIX)gcc
CPP := $(CROSS_PREFIX)cpp
AR := $(CROSS_PREFIX)ar
LD := $(CC)
OBJCOPY := $(CROSS_PREFIX)objcopy
SIZE := $(CROSS_PREFIX)size

#################
# Common config #
#################
CFLAGS += \
	$(ARCH_FLAGS) \
	-Wall \
	-Wextra \
	-Wpedantic \
	-Werror \
	-Wmissing-prototypes \
	-Wredundant-decls \
	-Wshadow \
	-Wpointer-arith \
	-Wno-unknown-pragmas \
	-O3 \
	-fomit-frame-pointer \
	-pedantic \
	-MMD \
	-I mlkem \
	-I fips202 \
	$(CPPFLAGS)

LDFLAGS += $(ARCH_FLAGS) 

LINKDEPS += $(LIBDEPS)

##################
# Some Variables #
##################
Q ?= @
QEMU = qemu-aarch64

HOST_PLATFORM := $(shell uname -s)-$(shell uname -m)
ifeq ($(HOST_PLATFORM),Linux-x86_64)
	CFLAGS += -static
endif

CYCLES ?= NO

ifeq ($(CYCLES),PMU)
	CFLAGS += -DPMU_CYCLES
endif

ifeq ($(CYCLES),PERF)
	CFLAGS += -DPERF_CYCLES
endif

ifeq ($(CYCLES),M1)
	CFLAGS += -DM1_CYCLES
endif

##############################
# Include retained variables #
##############################

RNG ?= 
RETAINED_VARS := RNG BENCH CYCLES

BUILD_DIR := test/build
LIB_DIR := $(BUILD_DIR)/lib

MAKE_OBJS = $(2:%=$(1)/%.o)
OBJS = $(call MAKE_OBJS,$(BUILD_DIR),$(1))

CONFIG := $(BUILD_DIR)/config.mk

-include $(CONFIG)

$(CONFIG):
	@echo "  GEN     $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	@echo "# These variables are retained and can't be changed without a clean" > $@
	@$(foreach var,$(RETAINED_VARS),echo "$(var) := $($(var))" >> $@; echo "LAST_$(var) := $($(var))" >> $@;)

define VAR_CHECK
ifneq ($$(origin LAST_$(1)),undefined)
ifneq "$$($(1))" "$$(LAST_$(1))"
$$(info Variable $(1) changed, forcing rebuild!)
.PHONY: $(CONFIG)
endif
endif
endef

$(foreach VAR,$(RETAINED_VARS),$(eval $(call VAR_CHECK,$(VAR))))
endif
