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
	$(MLKEM512_BUILD_DIR)/bin/test_kyber512_$(OPT_SUFFIX) \
	$(MLKEM768_BUILD_DIR)/bin/test_kyber768_$(OPT_SUFFIX) \
	$(MLKEM1024_BUILD_DIR)/bin/test_kyber1024_$(OPT_SUFFIX)

bench: \
	$(MLKEM512_BUILD_DIR)/bin/bench_kyber512_$(OPT_SUFFIX) \
	$(MLKEM768_BUILD_DIR)/bin/bench_kyber768_$(OPT_SUFFIX) \
	$(MLKEM1024_BUILD_DIR)/bin/bench_kyber1024_$(OPT_SUFFIX)

bench_components: \
	$(MLKEM512_BUILD_DIR)/bin/bench_components_kyber512_$(OPT_SUFFIX) \
	$(MLKEM768_BUILD_DIR)/bin/bench_components_kyber768_$(OPT_SUFFIX) \
	$(MLKEM1024_BUILD_DIR)/bin/bench_components_kyber1024_$(OPT_SUFFIX)

nistkat: \
	$(MLKEM512_BUILD_DIR)/bin/gen_NISTKAT512_$(OPT_SUFFIX) \
	$(MLKEM768_BUILD_DIR)/bin/gen_NISTKAT768_$(OPT_SUFFIX) \
	$(MLKEM1024_BUILD_DIR)/bin/gen_NISTKAT1024_$(OPT_SUFFIX)

kat: \
	$(MLKEM512_BUILD_DIR)/bin/gen_KAT512_$(OPT_SUFFIX) \
	$(MLKEM768_BUILD_DIR)/bin/gen_KAT768_$(OPT_SUFFIX) \
	$(MLKEM1024_BUILD_DIR)/bin/gen_KAT1024_$(OPT_SUFFIX)

# emulate ARM64 binary on x86_64 machine
emulate:
	$(Q)$(MAKE) --quiet CROSS_PREFIX=aarch64-none-linux-gnu- $(TARGET)
	$(Q)$(QEMU) $(TARGET)

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf $(BUILD_DIR)
