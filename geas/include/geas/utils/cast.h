#ifndef GEAS_CAST__H
#define GEAS_CAST__H
// Mapping different types to/from bit sequences.
#include <cstring>
#include <cfloat>

namespace cast {

// This _should_ be optimized away to a no-op.
static uint32_t s32 = (1<<31);
static uint64_t s64 = (((uint64_t) 1)<<63);

static uint32_t m32 = 0x80000000;
static uint64_t m64 = 0x8000000000000000;


template<class T, class U>
T conv(const U& x) {
  static_assert(sizeof(T) == sizeof(U),
    "Should bit-cast between values of equal size");
  T ret;
  memcpy(&ret, &x, sizeof(U));
  return ret;
}

inline uint64_t from_float(float v) {
  uint32_t bits = conv<uint32_t, float>(v); 
  // return (bits&s32) ? ((bits&m32)-bits) : bits;
  if(bits&s32) bits = m32 - bits;
  return bits^s32;
}

inline float to_float(uint64_t p) {
  uint32_t x(p);
  x = x^s32;
  if(x&s32) x = m32 - x;
  return conv<float, uint32_t>(x);
}

};
#endif
