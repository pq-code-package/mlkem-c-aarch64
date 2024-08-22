# SPDX-License-Identifier: Apache-2.0
SOURCES = $(wildcard mlkem/*.c)
OBJS = $(SOURCES:%.c=$(1)/%.o)

CPPFLAGS += -Imlkem
TESTS = test_kyber bench_kyber gen_NISTKAT gen_KAT

MLKEM512_DIR = $(BUILD_DIR)/mlkem512
MLKEM768_DIR = $(BUILD_DIR)/mlkem768
MLKEM1024_DIR = $(BUILD_DIR)/mlkem1024

$(MLKEM512_DIR)/bin/%: CPPFLAGS += -DKYBER_K=2
$(TESTS:%=$(MLKEM512_DIR)/bin/%):$(MLKEM512_DIR)/bin/%: $(MLKEM512_DIR)/test/%.o $(call OBJS,$(MLKEM512_DIR))

$(MLKEM768_DIR)/bin/%: CPPFLAGS += -DKYBER_K=3
$(TESTS:%=$(MLKEM768_DIR)/bin/%):$(MLKEM768_DIR)/bin/%: $(MLKEM768_DIR)/test/%.o $(call OBJS,$(MLKEM768_DIR))

$(MLKEM1024_DIR)/bin/%: CPPFLAGS += -DKYBER_K=4
$(TESTS:%=$(MLKEM1024_DIR)/bin/%):$(MLKEM1024_DIR)/bin/%: $(MLKEM1024_DIR)/test/%.o  $(call OBJS,$(MLKEM1024_DIR))
