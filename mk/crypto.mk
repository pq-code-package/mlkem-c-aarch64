# SPDX-License-Identifier: Apache-2.0
LDLIBS += -L$(LIB_DIR)

LIBDEPS += $(LIB_DIR)/libfips202.a
LDLIBS += -lfips202
CPPFLAGS += -Ifips202 -Ifips202/native

FIPS202_SRCS = $(wildcard fips202/*.c)
ifeq ($(OPT),1)
	FIPS202_SRCS += $(wildcard fips202/native/aarch64/*.S) $(wildcard fips202/native/x86_64/xkcp/*.c)
	CPPFLAGS += -DMLKEM_USE_NATIVE
endif

$(LIB_DIR)/libfips202.a: $(call OBJS, $(FIPS202_SRCS))
