# SPDX-License-Identifier: Apache-2.0
SOURCES = $(wildcard mlkem/*.c) $(wildcard mlkem/debug/*.c)
ifeq ($(OPT),1)
	SOURCES += $(wildcard mlkem/native/aarch64/*.[csS]) $(wildcard mlkem/native/x86_64/*.[csS])
	OPT_SUFFIX=opt
else
	OPT_SUFFIX=ref
endif

CPPFLAGS += -Imlkem -Imlkem/sys -Imlkem/native -Imlkem/native/aarch64 -Imlkem/native/x86_64
TESTS = test_kyber bench_kyber bench_components_kyber gen_NISTKAT gen_KAT

MLKEM512_BUILD_DIR = $(BUILD_DIR)/mlkem512
MLKEM768_BUILD_DIR = $(BUILD_DIR)/mlkem768
MLKEM1024_BUILD_DIR = $(BUILD_DIR)/mlkem1024

$(MLKEM512_BUILD_DIR)/bin/%: CPPFLAGS += -DKYBER_K=2
$(TESTS:%=$(MLKEM512_BUILD_DIR)/bin/%512_$(OPT_SUFFIX)):$(MLKEM512_BUILD_DIR)/bin/%512_$(OPT_SUFFIX): $(MLKEM512_BUILD_DIR)/test/%.c.o $(call MAKE_OBJS,$(MLKEM512_BUILD_DIR),$(SOURCES))

$(MLKEM768_BUILD_DIR)/bin/%: CPPFLAGS += -DKYBER_K=3
$(TESTS:%=$(MLKEM768_BUILD_DIR)/bin/%768_$(OPT_SUFFIX)):$(MLKEM768_BUILD_DIR)/bin/%768_$(OPT_SUFFIX): $(MLKEM768_BUILD_DIR)/test/%.c.o $(call MAKE_OBJS,$(MLKEM768_BUILD_DIR),$(SOURCES))

$(MLKEM1024_BUILD_DIR)/bin/%: CPPFLAGS += -DKYBER_K=4
$(TESTS:%=$(MLKEM1024_BUILD_DIR)/bin/%1024_$(OPT_SUFFIX)):$(MLKEM1024_BUILD_DIR)/bin/%1024_$(OPT_SUFFIX): $(MLKEM1024_BUILD_DIR)/test/%.c.o  $(call MAKE_OBJS,$(MLKEM1024_BUILD_DIR),$(SOURCES))
