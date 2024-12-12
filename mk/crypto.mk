# SPDX-License-Identifier: Apache-2.0
CPPFLAGS += -Ifips202 -Ifips202/native
FIPS202_SRCS = $(wildcard fips202/*.c)
ifeq ($(OPT),1)
	FIPS202_SRCS += $(wildcard fips202/native/aarch64/*.S) $(wildcard fips202/native/x86_64/xkcp/*.c)
endif

$(TMP_DIR)/libtmp_fips202.a: $(call OBJS, $(FIPS202_SRCS))
$(TMP_DIR)/libtmp_mlkem.a: $(call OBJS, $(FIPS202_SRCS))

# all lib<scheme>.a depends on libfips202.a
define ADD_FIPS202
$(TMP_DIR)/libtmp_$(1).a: LDLIBS += -ltmp_fips202
# NOTE:
# - Merging multiple .a files with ar is more complex than building a single library directly from all the object files (.o). Hence, all .o files are added as dependencies here.

$(TMP_DIR)/libtmp_$(1).a: $(TMP_DIR)/libtmp_fips202.a $(call OBJS, $(FIPS202_SRCS))
endef

$(foreach scheme,mlkem512 mlkem768 mlkem1024, \
	$(eval $(call ADD_FIPS202,$(scheme))) \
)
