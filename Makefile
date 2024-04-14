CC ?= /usr/bin/cc
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
HEADERS = mlkem/params.h mlkem/kem.h mlkem/indcpa.h mlkem/polyvec.h mlkem/poly.h mlkem/ntt.h mlkem/cbd.h mlkem/reduce.c mlkem/verify.h mlkem/symmetric.h
HEADERSKECCAK = $(HEADERS) fips202/keccakf1600.h fips202/fips202.h
NISTKATS = test/nistrng/aes.c test/nistrng/rng.c
NISTKATHEADERS = test/nistrng/aes.h test/nistrng/randombytes.h

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

test/test_kyber512: $(SOURCESKECCAK) $(HEADERSKECCAK) test/test_kyber.c randombytes/randombytes.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=2 $(SOURCESKECCAK) randombytes/randombytes.c test/test_kyber.c -o $@

test/test_kyber768: $(SOURCESKECCAK) $(HEADERSKECCAK) test/test_kyber.c randombytes/randombytes.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=3 $(SOURCESKECCAK) randombytes/randombytes.c test/test_kyber.c -o $@

test/test_kyber1024: $(SOURCESKECCAK) $(HEADERSKECCAK) test/test_kyber.c randombytes/randombytes.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=4 $(SOURCESKECCAK) randombytes/randombytes.c test/test_kyber.c -o $@

test/gen_NISTKAT512: $(SOURCESKECCAK) $(HEADERSKECCAK) test/gen_NISTKAT.c $(NISTKATS) $(NISTKATHEADERS)
	$(CC) $(CFLAGS_NISTRANDOMBYTES) -DKYBER_K=2 $(SOURCESKECCAK) $(NISTKATS) test/gen_NISTKAT.c -o $@

test/gen_NISTKAT768: $(SOURCESKECCAK) $(HEADERSKECCAK) test/gen_NISTKAT.c $(NISTKATS) $(NISTKATHEADERS)
	$(CC) $(CFLAGS_NISTRANDOMBYTES) -DKYBER_K=3 $(SOURCESKECCAK) $(NISTKATS) test/gen_NISTKAT.c -o $@

test/gen_NISTKAT1024: $(SOURCESKECCAK) $(HEADERSKECCAK) test/gen_NISTKAT.c $(NISTKATS) $(NISTKATHEADERS)
	$(CC) $(CFLAGS_NISTRANDOMBYTES) -DKYBER_K=4 $(SOURCESKECCAK) $(NISTKATS) test/gen_NISTKAT.c -o $@

test/gen_KAT512: $(SOURCESKECCAK) $(HEADERSKECCAK) test/gen_KAT.c randombytes/randombytes.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=2 $(SOURCESKECCAK) randombytes/randombytes.c test/gen_KAT.c -o $@

test/gen_KAT768: $(SOURCESKECCAK) $(HEADERSKECCAK) test/gen_KAT.c randombytes/randombytes.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=3 $(SOURCESKECCAK) randombytes/randombytes.c test/gen_KAT.c -o $@

test/gen_KAT1024: $(SOURCESKECCAK) $(HEADERSKECCAK) test/gen_KAT.c randombytes/randombytes.c
	$(CC) $(CFLAGS_RANDOMBYTES) -DKYBER_K=4 $(SOURCESKECCAK) randombytes/randombytes.c test/gen_KAT.c -o $@


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
