# SPDX-License-Identifier: Apache-2.0
CPPFLAGS += -Imlkem/fips202 -Imlkem/fips202/native
FIPS202_SRCS = $(wildcard mlkem/fips202/*.c)
ifeq ($(OPT),1)
	FIPS202_SRCS += $(wildcard mlkem/fips202/native/aarch64/src/*.S) $(wildcard mlkem/fips202/native/x86_64/src/*.c)
endif

$(BUILD_DIR)/libmlkem.a: $(call OBJS, $(FIPS202_SRCS))
$(BUILD_DIR)/libmlkem512.a: $(call OBJS, $(FIPS202_SRCS))
$(BUILD_DIR)/libmlkem768.a: $(call OBJS, $(FIPS202_SRCS))
$(BUILD_DIR)/libmlkem1024.a: $(call OBJS, $(FIPS202_SRCS))
