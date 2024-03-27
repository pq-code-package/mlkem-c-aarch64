CC ?= /usr/bin/cc
CFLAGS_FIPS202 = -I fips202
CFLAGS_MLKEM = -I mlkem
CFLAGS_RANDOMBYTES = -I randombytes
CFLAGS_TEST = -I test
CFLAGS += -Wall -Wextra -Wpedantic -Wmissing-prototypes -Wredundant-decls \
  -Wshadow -Wpointer-arith -O3 -fomit-frame-pointer -pedantic \
   ${CFLAGS_RANDOMBYTES} ${CFLAGS_MLKEM} ${CFLAGS_FIPS202} ${CFLAGS_TEST}
NISTFLAGS += -Wno-unused-result -O3 -fomit-frame-pointer
RM = /bin/rm

SOURCES = mlkem/kem.c mlkem/indcpa.c mlkem/polyvec.c mlkem/poly.c mlkem/ntt.c mlkem/cbd.c mlkem/reduce.c mlkem/verify.c
SOURCESKECCAK = $(SOURCES) fips202/keccakf1600.c fips202/fips202.c mlkem/symmetric-shake.c
HEADERS = mlkem/params.h mlkem/kem.h mlkem/indcpa.h mlkem/polyvec.h mlkem/poly.h mlkem/ntt.h mlkem/cbd.h mlkem/reduce.c mlkem/verify.h mlkem/symmetric.h
HEADERSKECCAK = $(HEADERS) fips202/keccakf1600.h fips202/fips202.h

.PHONY: all mlkem clean

all: mlkem

mlkem: \
  test/test_kyber512 \
  test/test_kyber768 \
  test/test_kyber1024

test/test_kyber512: $(SOURCESKECCAK) $(HEADERSKECCAK) test/test_kyber.c randombytes/randombytes.c
	$(CC) $(CFLAGS) -DKYBER_K=2 $(SOURCESKECCAK) randombytes/randombytes.c test/test_kyber.c -o $@

test/test_kyber768: $(SOURCESKECCAK) $(HEADERSKECCAK) test/test_kyber.c randombytes/randombytes.c
	$(CC) $(CFLAGS) -DKYBER_K=3 $(SOURCESKECCAK) randombytes/randombytes.c test/test_kyber.c -o $@

test/test_kyber1024: $(SOURCESKECCAK) $(HEADERSKECCAK) test/test_kyber.c randombytes/randombytes.c
	$(CC) $(CFLAGS) -DKYBER_K=4 $(SOURCESKECCAK) randombytes/randombytes.c test/test_kyber.c -o $@

clean:
	-$(RM) -rf *.gcno *.gcda *.lcov *.o *.so
	-$(RM) -rf test/test_kyber512
	-$(RM) -rf test/test_kyber768
	-$(RM) -rf test/test_kyber1024
