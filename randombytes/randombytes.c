// SPDX-License-Identifier: Apache-2.0
#include "randombytes.h"
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#ifdef _WIN32
#include <wincrypt.h>
#include <windows.h>
#else
#include <errno.h>
#include <fcntl.h>
#ifdef __linux__
#define _GNU_SOURCE
#include <sys/syscall.h>
#include <unistd.h>
#else
#include <unistd.h>
#endif
#endif

#ifdef _WIN32
void randombytes(uint8_t *out, size_t outlen) {
  HCRYPTPROV ctx;
  size_t len;

  if (!CryptAcquireContext(&ctx, NULL, NULL, PROV_RSA_FULL,
                           CRYPT_VERIFYCONTEXT)) {
    abort();
  }

  while (outlen > 0) {
    len = (outlen > 1048576) ? 1048576 : outlen;
    if (!CryptGenRandom(ctx, len, (BYTE *)out)) {
      abort();
    }

    out += len;
    outlen -= len;
  }

  if (!CryptReleaseContext(ctx, 0)) {
    abort();
  }
}
#elif defined(__linux__) && defined(SYS_getrandom)
void randombytes(uint8_t *out, size_t outlen) {
  ssize_t ret;

  while (outlen > 0) {
    ret = syscall(SYS_getrandom, out, outlen, 0);
    if (ret == -1 && errno == EINTR) {
      continue;
    } else if (ret == -1) {
      abort();
    }

    out += ret;
    outlen -= ret;
  }
}
#else
void randombytes(uint8_t *out, size_t outlen) {
  static int fd = -1;
  ssize_t ret;

  while (fd == -1) {
    fd = open("/dev/urandom", O_RDONLY);
    if (fd == -1 && errno == EINTR) {
      continue;
    } else if (fd == -1) {
      abort();
    }
  }

  while (outlen > 0) {
    ret = read(fd, out, outlen);
    if (ret == -1 && errno == EINTR) {
      continue;
    } else if (ret == -1) {
      abort();
    }

    out += ret;
    outlen -= ret;
  }
}
#endif
