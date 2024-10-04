// SPDX-License-Identifier: MIT

#if __APPLE__
#define ASM_LOAD(dst, symbol)                                                  \
  adrp dst, symbol @PAGE %% add dst, dst, symbol @PAGEOFF
#else /* __APPLE__ */
#define ASM_LOAD(dst, symbol)                                                  \
  adrp dst, symbol;                                                            \
  add dst, dst, : lo12 : symbol;
#endif /* !__APPLE__ */
