# SPDX-License-Identifier: Apache-2.0
BENCH = 1

LIBDEPS += $(LIB_DIR)/libhal.a
LDLIBS += -lhal
CPPFLAGS += -Itest/hal
$(LIB_DIR)/libhal.a: $(call OBJS,$(wildcard test/hal/*.c))
