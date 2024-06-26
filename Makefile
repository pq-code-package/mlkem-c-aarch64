# SPDX-License-Identifier: Apache-2.0


.PHONY: all mlkem kat nistkat clean

all: mlkem bench kat nistkat

include mk/config.mk

INCLUDE_RANDOM = -I randombytes
INCLUDE_NISTRANDOM = -I test/nistrng

CFLAGS_RANDOMBYTES = ${CFLAGS} ${INCLUDE_RANDOM}
CFLAGS_NISTRANDOMBYTES = ${CFLAGS} ${INCLUDE_NISTRANDOM}
NISTFLAGS += -Wno-unused-result -O3 -fomit-frame-pointer
RM = /bin/rm

SOURCES = mlkem/kem.c mlkem/indcpa.c mlkem/polyvec.c mlkem/poly.c mlkem/ntt.c mlkem/cbd.c mlkem/reduce.c mlkem/verify.c
SOURCESKECCAK = $(SOURCES) fips202/keccakf1600.c fips202/fips202.c mlkem/symmetric-shake.c
SOURCESKECCAKRANDOM = $(SOURCESKECCAK) randombytes/randombytes.c
SOURCESNISTKATS = $(SOURCESKECCAK) test/nistrng/aes.c test/nistrng/rng.c
SOURCESBENCH = $(SOURCESKECCAKRANDOM) test/hal.c

HEADERS = mlkem/params.h mlkem/kem.h mlkem/indcpa.h mlkem/polyvec.h mlkem/poly.h mlkem/ntt.h mlkem/cbd.h mlkem/reduce.h mlkem/verify.h mlkem/symmetric.h
HEADERSKECCAK = $(HEADERS) fips202/keccakf1600.h fips202/fips202.h
HEADERSKECCAKRANDOM = $(HEADERSKECCAK) randombytes/randombytes.h
HEADERNISTKATS = $(HEADERSKECCAK) test/nistrng/aes.h test/nistrng/randombytes.h
HEADERSBENCH = $(HEADERSKECCAKRANDOM) test/hal.h

mlkem: \
  test/bin/test_kyber512 \
  test/bin/test_kyber768 \
  test/bin/test_kyber1024

bench: \
  test/bin/bench_kyber512 \
  test/bin/bench_kyber768 \
  test/bin/bench_kyber1024

nistkat: \
  test/bin/gen_NISTKAT512 \
  test/bin/gen_NISTKAT768 \
  test/bin/gen_NISTKAT1024

kat: \
  test/bin/gen_KAT512 \
  test/bin/gen_KAT768 \
  test/bin/gen_KAT1024

test/bin/test_kyber512: test/test_kyber.c $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=2 $(SOURCESKECCAKRANDOM) $< -o $@

test/bin/test_kyber768: test/test_kyber.c $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=3 $(SOURCESKECCAKRANDOM) $< -o $@

test/bin/test_kyber1024: test/test_kyber.c $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=4 $(SOURCESKECCAKRANDOM) $< -o $@

test/bin/bench_kyber512: test/bench_kyber.c $(SOURCESBENCH) $(HEADERSBENCH) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=2 $(SOURCESBENCH) $< -o $@

test/bin/bench_kyber768: test/bench_kyber.c $(SOURCESBENCH) $(HEADERSBENCH) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=3 $(SOURCESBENCH) $< -o $@

test/bin/bench_kyber1024: test/bench_kyber.c $(SOURCESBENCH) $(HEADERSBENCH) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=4 $(SOURCESBENCH) $< -o $@

test/bin/gen_KAT512: test/gen_KAT.c $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=2 $(SOURCESKECCAKRANDOM) $< -o $@

test/bin/gen_KAT768: test/gen_KAT.c $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=3 $(SOURCESKECCAKRANDOM) $< -o $@

test/bin/gen_KAT1024: test/gen_KAT.c $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=4 $(SOURCESKECCAKRANDOM) $< -o $@

test/bin/gen_NISTKAT512: test/gen_NISTKAT.c $(SOURCESNISTKATS) $(HEADERNISTKATS) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_NISTRANDOMBYTES) -DKYBER_K=2 $(SOURCESNISTKATS) $< -o $@

test/bin/gen_NISTKAT768: test/gen_NISTKAT.c $(SOURCESNISTKATS) $(HEADERNISTKATS) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_NISTRANDOMBYTES) -DKYBER_K=3 $(SOURCESNISTKATS) $< -o $@

test/bin/gen_NISTKAT1024: test/gen_NISTKAT.c $(SOURCESNISTKATS) $(HEADERNISTKATS) $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(CC) $(CFLAGS_NISTRANDOMBYTES) -DKYBER_K=4 $(SOURCESNISTKATS) $< -o $@

# emulate ARM64 binary on x86_64 machine
emulate:
	$(Q)$(MAKE) --quiet CROSS_PREFIX=aarch64-none-linux-gnu- $(TARGET)
	$(Q)$(QEMU) $(TARGET)

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf test/bin
	-$(RM) -rf test/obj
