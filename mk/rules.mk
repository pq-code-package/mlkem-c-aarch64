# SPDX-License-Identifier: Apache-2.0
$(BUILD_DIR)/%: $(LINKDEPS) $(CONFIG)
	$(Q)echo "  LD      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(LD) $(LDFLAGS) -o $@ $(filter %.o,$^) $(LDLIBS)

$(LIB_DIR)/%.a: $(CONFIG)
	$(Q)echo "  AR      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)rm -f $@
	$(Q)$(AR) rcs $@ $(filter %.o,$^)

$(BUILD_DIR)/%.o: %.c $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/%.c.o: %.c $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/mlkem512/%.o: %.c $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/mlkem512/%.c.o: %.c $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/mlkem768/%.o: %.c $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/mlkem768/%.c.o: %.c $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/mlkem1024/%.o: %.c $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<

$(BUILD_DIR)/mlkem1024/%.c.o: %.c $(CONFIG)
	$(Q)echo "  CC      $@"
	$(Q)[ -d $(@D) ] || mkdir -p $(@D)
	$(Q)$(CC) -c -o $@ $(CFLAGS) $<
