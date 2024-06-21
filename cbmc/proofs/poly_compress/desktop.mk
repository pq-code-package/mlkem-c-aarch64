# SPDX-License-Identifier: Apache-2.0

FILE = ../../../mlkem/poly
HARNESS_FILE = poly_compress_harness
TARGET ?= pqcrystals_kyber768_ref_poly_compress

CHECKS=--bounds-check --pointer-check \
       --memory-cleanup-check --div-by-zero-check --signed-overflow-check \
       --unsigned-overflow-check --pointer-overflow-check --conversion-check \
       --undefined-shift-check --enum-range-check --pointer-primitive-check

all: clean $(TARGET)

pqcrystals_kyber768_ref_poly_compress: $(FILE)_contracts.goto results_smt


results_smt: $(FILE)_contracts.goto
	cbmc --verbosity 6 --object-bits 10 $(CHECKS) --smt2 $<

$(FILE)_contracts.goto: $(FILE).goto
	goto-instrument --dfcc harness --apply-loop-contracts --enforce-contract $(TARGET) --replace-call-with-contract pqcrystals_kyber768_ref_scalar_compress_q_16 --replace-call-with-contract pqcrystals_kyber768_ref_scalar_compress_q_32 --replace-call-with-contract coeff_signed_to_unsigned $< $@

$(FILE).goto: $(FILE).c $(HARNESS_FILE).c
	goto-cc --function harness -DCBMC -I../../../fips202 -I../../../mlkem -o $@ $^

clean:
	rm -f *.goto
