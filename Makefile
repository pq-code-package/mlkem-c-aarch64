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
  $(MLKEM512_DIR)/bin/test_kyber512 \
  $(MLKEM768_DIR)/bin/test_kyber768 \
  $(MLKEM1024_DIR)/bin/test_kyber1024 \

bench:
	$(MAKE) $(MAKEFLAGS) BENCH=1 $(MLKEM512_DIR)/bin/bench_kyber512
	$(MAKE) $(MAKEFLAGS) BENCH=1 $(MLKEM768_DIR)/bin/bench_kyber768
	$(MAKE) $(MAKEFLAGS) BENCH=1 $(MLKEM1024_DIR)/bin/bench_kyber1024

nistkat:
	$(MAKE) $(MAKEFLAGS) RNG=NISTRNG $(MLKEM512_DIR)/bin/gen_NISTKAT512
	$(MAKE) $(MAKEFLAGS) RNG=NISTRNG $(MLKEM768_DIR)/bin/gen_NISTKAT768
	$(MAKE) $(MAKEFLAGS) RNG=NISTRNG $(MLKEM1024_DIR)/bin/gen_NISTKAT1024

kat: \
  $(MLKEM512_DIR)/bin/gen_KAT512 \
  $(MLKEM768_DIR)/bin/gen_KAT768 \
  $(MLKEM1024_DIR)/bin/gen_KAT1024

# emulate ARM64 binary on x86_64 machine
emulate:
	$(Q)$(MAKE) --quiet CROSS_PREFIX=aarch64-none-linux-gnu- $(TARGET)
	$(Q)$(QEMU) $(TARGET)

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf $(BUILD_DIR)
