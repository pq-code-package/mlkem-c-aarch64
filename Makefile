# SPDX-License-Identifier: Apache-2.0

CC ?= gcc
INCLUDE_FIPS202 = -I fips202
INCLUDE_MLKEM = -I mlkem
INCLUDE_RANDOM = -I randombytes
INCLUDE_NISTRANDOM = -I test/nistrng
CFLAGS += -Wall -Wextra -Wpedantic -Wmissing-prototypes -Wredundant-decls \
  -Wshadow -Wpointer-arith -O3 -fomit-frame-pointer -pedantic \
   ${INCLUDE_MLKEM} ${INCLUDE_FIPS202}
CFLAGS_RANDOMBYTES = ${CFLAGS} ${INCLUDE_RANDOM}
CFLAGS_NISTRANDOMBYTES = ${CFLAGS} ${INCLUDE_NISTRANDOM}
NISTFLAGS += -Wno-unused-result -O3 -fomit-frame-pointer
RM = /bin/rm

SOURCES = mlkem/kem.c mlkem/indcpa.c mlkem/polyvec.c mlkem/poly.c mlkem/ntt.c mlkem/cbd.c mlkem/reduce.c mlkem/verify.c
SOURCESKECCAK = $(SOURCES) fips202/keccakf1600.c fips202/fips202.c mlkem/symmetric-shake.c
SOURCESKECCAKRANDOM = $(SOURCESKECCAK) randombytes/randombytes.c
SOURCESNISTKATS = $(SOURCESKECCAK) test/nistrng/aes.c test/nistrng/rng.c

HEADERS = mlkem/params.h mlkem/kem.h mlkem/indcpa.h mlkem/polyvec.h mlkem/poly.h mlkem/ntt.h mlkem/cbd.h mlkem/reduce.c mlkem/verify.h mlkem/symmetric.h
HEADERSKECCAK = $(HEADERS) fips202/keccakf1600.h fips202/fips202.h
HEADERSKECCAKRANDOM = $(HEADERSKECCAK) randombytes/randombytes.h
HEADERNISTKATS = $(HEADERSKECCAK) test/nistrng/aes.h test/nistrng/randombytes.h

.PHONY: all mlkem kat nistkat clean

all: mlkem kat nistkat

mlkem: \
  test/test_kyber512 \
  test/test_kyber768 \
  test/test_kyber1024

nistkat: \
  test/gen_NISTKAT512 \
  test/gen_NISTKAT768 \
  test/gen_NISTKAT1024

kat: \
  test/gen_KAT512 \
  test/gen_KAT768 \
  test/gen_KAT1024

test/test_kyber512: $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) test/test_kyber.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=2 $(SOURCESKECCAKRANDOM) test/test_kyber.c -o $@

test/test_kyber768: $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) test/test_kyber.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=3 $(SOURCESKECCAKRANDOM) test/test_kyber.c -o $@

test/test_kyber1024: $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) test/test_kyber.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=4 $(SOURCESKECCAKRANDOM) test/test_kyber.c -o $@

test/gen_KAT512: $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) test/gen_KAT.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=2 $(SOURCESKECCAKRANDOM) test/gen_KAT.c -o $@

test/gen_KAT768: $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) test/gen_KAT.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=3 $(SOURCESKECCAKRANDOM) test/gen_KAT.c -o $@

test/gen_KAT1024: $(SOURCESKECCAKRANDOM) $(HEADERSKECCAKRANDOM) test/gen_KAT.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=4 $(SOURCESKECCAKRANDOM) test/gen_KAT.c -o $@

test/gen_NISTKAT512: $(SOURCESNISTKATS) $(HEADERNISTKATS) test/gen_NISTKAT.c
	$(CC) $(CFLAGS_NISTRANDOMBYTES) -DKYBER_K=2 $(SOURCESNISTKATS) test/gen_NISTKAT.c -o $@

test/gen_NISTKAT768: $(SOURCESNISTKATS) $(HEADERNISTKATS) test/gen_NISTKAT.c
	$(CC) $(CFLAGS_NISTRANDOMBYTES) -DKYBER_K=3 $(SOURCESNISTKATS) test/gen_NISTKAT.c -o $@

test/gen_NISTKAT1024: $(SOURCESNISTKATS) $(HEADERNISTKATS) test/gen_NISTKAT.c
	$(CC) $(CFLAGS_NISTRANDOMBYTES) -DKYBER_K=4 $(SOURCESNISTKATS) test/gen_NISTKAT.c -o $@


clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf test/test_kyber512
	-$(RM) -rf test/test_kyber768
	-$(RM) -rf test/test_kyber1024
	-$(RM) -rf test/gen_KAT512
	-$(RM) -rf test/gen_KAT768
	-$(RM) -rf test/gen_KAT1024
	-$(RM) -rf test/gen_NISTKAT512
	-$(RM) -rf test/gen_NISTKAT768
	-$(RM) -rf test/gen_NISTKAT1024
