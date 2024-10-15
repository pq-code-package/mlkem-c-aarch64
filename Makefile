# SPDX-License-Identifier: Apache-2.0


.PHONY: mlkem kat nistkat clean quickcheck buildall

buildall:
	$(Q)$(MAKE) mlkem
	$(Q)$(MAKE) nistkat
	$(Q)$(MAKE) kat
	$(Q)echo "  ALL GOOD!"

include mk/config.mk
-include mk/$(MAKECMDGOALS).mk
include mk/crypto.mk
include mk/schemes.mk
include mk/rules.mk

quickcheck:
	$(Q)$(MAKE) mlkem
	$(MLKEM512_DIR)/bin/test_kyber512
	$(MLKEM768_DIR)/bin/test_kyber768
	$(MLKEM1024_DIR)/bin/test_kyber1024
	$(Q)$(MAKE) nistkat
	$(MLKEM512_DIR)/bin/gen_NISTKAT512
	$(MLKEM768_DIR)/bin/gen_NISTKAT768
	$(MLKEM1024_DIR)/bin/gen_NISTKAT1024
	$(Q)$(MAKE) kat
	$(MLKEM512_DIR)/bin/gen_KAT512
	$(MLKEM768_DIR)/bin/gen_KAT768
	$(MLKEM1024_DIR)/bin/gen_KAT1024
	$(Q)echo "  ALL GOOD!"

mlkem: \
  $(MLKEM512_DIR)/bin/test_kyber512 \
  $(MLKEM768_DIR)/bin/test_kyber768 \
  $(MLKEM1024_DIR)/bin/test_kyber1024

bench: \
	$(MLKEM512_DIR)/bin/bench_kyber512 \
	$(MLKEM768_DIR)/bin/bench_kyber768 \
	$(MLKEM1024_DIR)/bin/bench_kyber1024

bench_components: \
	$(MLKEM512_DIR)/bin/bench_components_kyber512 \
	$(MLKEM768_DIR)/bin/bench_components_kyber768 \
	$(MLKEM1024_DIR)/bin/bench_components_kyber1024

nistkat: \
	$(MLKEM512_DIR)/bin/gen_NISTKAT512 \
	$(MLKEM768_DIR)/bin/gen_NISTKAT768 \
	$(MLKEM1024_DIR)/bin/gen_NISTKAT1024

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
