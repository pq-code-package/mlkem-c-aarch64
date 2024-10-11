# SPDX-License-Identifier: Apache-2.0
#
# Automatically detect system architecture and set preprocessor etc accordingly
ifeq ($(HOST_PLATFORM),Linux-x86_64)
ifeq ($(CROSS_PREFIX),)
	ARCH_FLAGS += -mavx2 -mbmi2 -mpopcnt -maes
	CFLAGS += -DFORCE_X86_64
else ifneq ($(findstring aarch64, $(CROSS_PREFIX)),)
	CFLAGS += -DFORCE_AARCH64
else

endif

# linux aarch64
else ifeq ($(HOST_PLATFORM),Linux-aarch64)
ifeq ($(CROSS_PREFIX),)
	CFLAGS += -DFORCE_AARCH64
else ifneq ($(findstring x86_64, $(CROSS_PREFIX)),)
	ARCH_FLAGS += -mavx2 -mbmi2 -mpopcnt -maes
	CFLAGS += -DFORCE_X86_64
else
endif

# darwin aarch64
else ifeq ($(HOST_PLATFORM),Darwin-arm64)
	CFLAGS += -DFORCE_AARCH64
endif
