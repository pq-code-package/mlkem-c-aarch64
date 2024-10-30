# SPDX-License-Identifier: Apache-2.0
LDLIBS += -L$(LIB_DIR)

LIBDEPS += $(LIB_DIR)/libfips202.a $(LIB_DIR)/libnistrng.a $(LIB_DIR)/librng.a
LDLIBS += -lfips202
CPPFLAGS += -Ifips202 -Ifips202/native

FIPS202_SRCS = $(wildcard fips202/*.c)
ifeq ($(OPT),1)
	FIPS202_SRCS += $(wildcard fips202/native/aarch64/*.S) $(wildcard fips202/native/x86_64/xkcp/*.c)
	CPPFLAGS += -DMLKEM_USE_NATIVE
endif

$(LIB_DIR)/libnistrng.a: CPPFLAGS += -Itest/notrandombytes
$(LIB_DIR)/librng.a: $(call OBJS,$(wildcard test/notrandombytes/*.c))

$(LIB_DIR)/libnistrng.a: CPPFLAGS += -Itest/nistrng
$(LIB_DIR)/libnistrng.a: CFLAGS += -Wno-unused-result -O3 -fomit-frame-pointer
$(LIB_DIR)/libnistrng.a: $(call OBJS,$(wildcard test/nistrng/*.c))

$(LIB_DIR)/libfips202.a: $(call OBJS, $(FIPS202_SRCS))
