# SPDX-License-Identifier: Apache-2.0


.PHONY: all mlkem kat nistkat clean

all: mlkem bench kat nistkat

include mk/config.mk
include mk/crypto.mk
include mk/schemes.mk
include mk/hal.mk
include mk/rules.mk

MAKEFLAGS = --no-print-directory

mlkem: \
  $(MLKEM512_DIR)/bin/test_kyber \
  $(MLKEM768_DIR)/bin/test_kyber \
  $(MLKEM1024_DIR)/bin/test_kyber \

bench:
	$(MAKE) $(MAKEFLAGS) BENCH=1 $(MLKEM512_DIR)/bin/bench_kyber
	$(MAKE) $(MAKEFLAGS) BENCH=1 $(MLKEM768_DIR)/bin/bench_kyber
	$(MAKE) $(MAKEFLAGS) BENCH=1 $(MLKEM1024_DIR)/bin/bench_kyber

nistkat:
	$(MAKE) $(MAKEFLAGS) RNG=NISTRNG $(MLKEM512_DIR)/bin/gen_NISTKAT
	$(MAKE) $(MAKEFLAGS) RNG=NISTRNG $(MLKEM768_DIR)/bin/gen_NISTKAT
	$(MAKE) $(MAKEFLAGS) RNG=NISTRNG $(MLKEM1024_DIR)/bin/gen_NISTKAT

kat: \
  $(MLKEM512_DIR)/bin/gen_KAT \
  $(MLKEM768_DIR)/bin/gen_KAT \
  $(MLKEM1024_DIR)/bin/gen_KAT

# emulate ARM64 binary on x86_64 machine
emulate:
	$(Q)$(MAKE) --quiet CROSS_PREFIX=aarch64-none-linux-gnu- $(TARGET)
	$(Q)$(QEMU) $(TARGET)

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf $(BUILD_DIR)
