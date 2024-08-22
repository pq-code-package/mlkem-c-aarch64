# SPDX-License-Identifier: Apache-2.0
ifdef BENCH

LIBDEPS += $(LIB_DIR)/libhal.a
LDLIBS += -lhal
CPPFLAGS += -Itest/hal
$(LIB_DIR)/libhal.a: $(call objs,$(wildcard test/hal/*.c))

endif
