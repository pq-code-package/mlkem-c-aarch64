# SPDX-License-Identifier: Apache-2.0
CPPFLAGS += -Ifips202 -Ifips202/native

SOURCES += $(wildcard fips202/*.c)
ifeq ($(OPT),1)
	SOURCES += $(wildcard fips202/native/aarch64/*.S) $(wildcard fips202/native/x86_64/xkcp/*.c)
endif
