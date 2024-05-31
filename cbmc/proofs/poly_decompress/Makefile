# SPDX-License-Identifier: Apache-2.0

include ../Makefile_params.common

HARNESS_ENTRY = harness
HARNESS_FILE = poly_decompress_harness

# This should be a unique identifier for this proof, and will appear on the
# Litani dashboard. It can be human-readable and contain spaces if you wish.
PROOF_UID = poly_decompress

DEFINES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROJECT_SOURCES += $(SRCDIR)/mlkem/poly.c

# For KYBER_K=2,3 a loop with 128 iterations is used.
# For KYBER_K=4, a nested loop with 32 and 8 iterations is used.
ifneq ($(KYBER_K),4)
	UNWINDSET += $(KYBER_NAMESPACE)poly_decompress.0:129
else
	UNWINDSET += $(KYBER_NAMESPACE)poly_decompress.1:33
	UNWINDSET += $(KYBER_NAMESPACE)poly_decompress.0:9
endif

FUNCTION_NAME = $(KYBER_NAMESPACE)poly_decompress

# TODO: I would like to comment this out to have CBMC validate the
# function contract as annotated in the source, rather than being forced
# to replicate it in the harness. But somehow this doesn't work...?

# USE_FUNCTION_CONTRACTS = $(FUNCTION_NAME)

# USE_DYNAMIC_FRAMES = 1
# EXTERNAL_SAT_SOLVER = cadical
# CBMCFLAGS += --smt2

# If this proof is found to consume huge amounts of RAM, you can set the
# EXPENSIVE variable. With new enough versions of the proof tools, this will
# restrict the number of EXPENSIVE CBMC jobs running at once. See the
# documentation in Makefile.common under the "Job Pools" heading for details.
# EXPENSIVE = true

# If you require access to a file-local ("static") function or object to conduct
# your proof, set the following (and do not include the original source file
# ("mlkem/poly.c") in PROJECT_SOURCES).
# REWRITTEN_SOURCES = $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i
# include ../Makefile.common
# $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i_SOURCE = $(SRCDIR)/mlkem/poly.c
# $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i_FUNCTIONS = foo bar
# $(PROOFDIR)/<__SOURCE_FILE_BASENAME__>.i_OBJECTS = baz
# Care is required with variables on the left-hand side: REWRITTEN_SOURCES must
# be set before including Makefile.common, but any use of variables on the
# left-hand side requires those variables to be defined. Hence, _SOURCE,
# _FUNCTIONS, _OBJECTS is set after including Makefile.common.

include ../Makefile.common
