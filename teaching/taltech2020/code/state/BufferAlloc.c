
/* This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
 * KreMLin invocation: /Users/danel/KreMLin/krml BufferAlloc.fst
 * F* version: 43fbe5dc
 * KreMLin version: a3d914df
 */

#include "BufferAlloc.h"

uint64_t BufferAlloc_f()
{
  uint64_t b[64U];
  for (uint32_t _i = 0U; _i < (uint32_t)64U; ++_i)
    b[_i] = (uint64_t)1U;
  b[42U] = b[42U] + (uint64_t)42U;
  uint64_t r = b[42U];
  return r;
}
