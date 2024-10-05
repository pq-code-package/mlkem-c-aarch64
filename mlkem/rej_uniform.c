// SPDX-License-Identifier: Apache-2.0
#include "params.h"

#include "arith_native.h"
#include "rej_uniform.h"

/*************************************************
 * Name:        rej_uniform_scalar
 *
 * Description: Run rejection sampling on uniform random bytes to generate
 *              uniform random integers mod q
 *
 * Arguments:   - int16_t *r:          pointer to output buffer
 *              - unsigned int len:    requested number of 16-bit integers
 *                                     (uniform mod q)
 *              - const uint8_t *buf:  pointer to input buffer
 *                                     (assumed to be uniform random bytes)
 *              - unsigned int buflen: length of input buffer in bytes
 *
 * Returns number of sampled 16-bit integers (at most len)
 **************************************************/
static unsigned int rej_uniform_scalar(int16_t *r, unsigned int len,
                                       const uint8_t *buf,
                                       unsigned int buflen) {
  unsigned int ctr, pos;
  uint16_t val0, val1;

  ctr = pos = 0;
  while (ctr < len && pos + 3 <= buflen) {
    val0 = ((buf[pos + 0] >> 0) | ((uint16_t)buf[pos + 1] << 8)) & 0xFFF;
    val1 = ((buf[pos + 1] >> 4) | ((uint16_t)buf[pos + 2] << 4)) & 0xFFF;
    pos += 3;

    if (val0 < KYBER_Q) {
      r[ctr++] = val0;
    }
    if (ctr < len && val1 < KYBER_Q) {
      r[ctr++] = val1;
    }
  }
  return ctr;
}

#if !defined(MLKEM_USE_NATIVE_AARCH64)
unsigned int rej_uniform(int16_t *r, unsigned int len, const uint8_t *buf,
                         unsigned int buflen) {
  return rej_uniform_scalar(r, len, buf, buflen);
}
#else  /* MLKEM_USE_NATIVE_AARCH64 */

/*************************************************
 * Name:        rej_uniform
 *
 * Description: Run rejection sampling on uniform random bytes to generate
 *              uniform random integers mod q
 *
 * Arguments:   - int16_t *r:          pointer to output buffer
 *              - unsigned int len:    requested number of 16-bit integers
 *                                     (uniform mod q)
 *              - const uint8_t *buf:  pointer to input buffer
 *                                     (assumed to be uniform random bytes)
 *              - unsigned int buflen: length of input buffer in bytes
 *
 * Returns number of sampled 16-bit integers (at most len)
 **************************************************/
unsigned int rej_uniform(int16_t *r, unsigned int len, const uint8_t *buf,
                         unsigned int buflen) {
  int ret;

  // Sample from large buffer with full lane as much as possible.
  ret = rej_uniform_native(r, len, buf, buflen);
  if (ret != -1)
    return (unsigned)ret;

  return rej_uniform_scalar(r, len, buf, buflen);
}
#endif /* MLKEM_USE_NATIVE_AARCH64 */
