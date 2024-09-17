# SPDX-License-Identifier: Apache-2.0
LDLIBS += -L$(LIB_DIR)

LIBDEPS += $(LIB_DIR)/libfips202.a
LDLIBS += -lfips202
CPPFLAGS += -Ifips202

ifeq ($(RNG),NISTRNG)
	LIBDEPS += $(LIB_DIR)/libnistrng.a
	LDLIBS += -lnistrng
	CPPFLAGS += -Itest/nistrng
else
	LIBDEPS += $(LIB_DIR)/librng.a
	LDLIBS += -lrng
	CPPFLAGS += -Irandombytes
endif

FIPS202_SRCS = $(wildcard fips202/*.c)
ifeq ($(OPT),1)
	FIPS202_SRCS += $(wildcard fips202/asm/aarch64/*.S)
	CPPFLAGS += -DMLKEM_USE_ASM
endif

$(LIB_DIR)/librng.a: $(call OBJS,$(wildcard randombytes/*.c))

$(LIB_DIR)/libnistrng.a: CFLAGS += -Wno-unused-result -O3 -fomit-frame-pointer
$(LIB_DIR)/libnistrng.a: $(call OBJS,$(wildcard test/nistrng/*.c))

$(LIB_DIR)/libfips202.a: $(call OBJS, $(FIPS202_SRCS))
