# SPDX-License-Identifier: Apache-2.0

LIBDEPS += $(LIB_DIR)/libhal.a
LDLIBS += -lhal
CPPFLAGS += -Itest/hal
$(LIB_DIR)/libhal.a: $(call OBJS,$(wildcard test/hal/*.c))
