// SPDX-License-Identifier: Apache-2.0
#ifndef REJ_UNIFORM_H
#define REJ_UNIFORM_H

#define rej_uniform KYBER_NAMESPACE(rej_uniform)
unsigned int rej_uniform(int16_t *r,
                         unsigned int len,
                         const uint8_t *buf,
                         unsigned int buflen);

#endif
