#ifndef GEAS__BITOPS__H
#define GEAS__BITOPS__H
// Helper header for doing stuff on BitMaps.
#include <cstring>
#include <stdint.h>

namespace geas {
  namespace B32 {
    inline unsigned block_bits(void) { return 5; }
    inline unsigned block_size(void) { return 1 << block_bits(); }
    inline uint64_t block_mask(void) { return block_size()-1; }
    inline unsigned req_words(unsigned sz) { return (sz >> block_bits()) + ((sz & block_mask()) != 0); }
    inline unsigned block(unsigned p) { return p >> block_bits(); }
    inline unsigned index(unsigned p) { return p & ((1<<block_bits())-1); }
    inline uint64_t bit(unsigned p) { return 1ull << index(p); }
  };

  // TODO: Factor all this stuff out
  namespace B64 {
    inline unsigned block_bits(void) { return 6; }
    inline unsigned block_size(void) { return 1 << block_bits(); }
    inline uint64_t block_mask(void) { return block_size()-1; }
    inline unsigned req_words(unsigned sz) { return (sz >> block_bits()) + ((sz & block_mask()) != 0); }
    inline unsigned block(unsigned p) { return p >> block_bits(); }
    inline unsigned index(unsigned p) { return p & ((1<<block_bits())-1); }
    inline uint64_t bit(unsigned p) { return 1ull << index(p); }

    inline void Fill_BV(uint64_t* start, unsigned sz) {
      memset(start, -1, sizeof(uint64_t) * req_words(sz));
      if(bit(sz))
        start[block(sz)] &= bit(sz)-1;
    }

    inline int Min_BV(uint64_t* start, int base = 0) {
      while(!*start) {
        ++start;
        base += 64;
      }
      return base + __builtin_ctzll(*start);
    }
    
    template<class F>
    inline void Iter_BV(uint64_t* b, uint64_t* e, F f, int base = 0) {
      for(; b != e; ++b) {
        uint64_t mask(*b);
        while(mask) {
          unsigned offset(__builtin_ctzll(mask));
          mask &= (mask-1);
          f(base + offset);
        }
        base += 64;
      }
    }

    template<class F>
      inline void Iter_Word(int base, uint64_t word, F f) {
      while(word) {
        unsigned offset(__builtin_ctzll(word));
        word &= (word-1);
        f(base + offset);
      }
    }
    template<class F>
      inline void Iter_Blocks(uint64_t* b, uint64_t* e, F f, int base = 0) {
       for(; b != e; ++b) {
        uint64_t mask(*b);
        if(mask)
          f(base, mask);
        base += 64;
      }
    }
    template<class F>
      inline bool Forall_Word(int base, uint64_t word, F f) {
      while(word) {
        unsigned offset(__builtin_ctzll(word));
        word &= (word-1);
        if(!f(base + offset))
          return false;
      }
      return true;
    }
    template<class F>
    inline bool Forall_BV(uint64_t* b, uint64_t* e, F f, int base = 0) {
      for(; b != e; ++b) {
        uint64_t mask(*b);
        while(mask) {
          unsigned offset(__builtin_ctzll(mask));
          mask &= (mask-1);
          if(!f(base + offset))
            return false;
        }
        base += 64;
      }
      return true;
    }
    template<class F>
      inline bool Forall_Blocks(uint64_t* b, uint64_t* e, F f, int base = 0) {
      for(; b != e; ++b) {
        uint64_t mask(*b);
        if(mask) {
          if(!f(base, mask))
            return false;
        }
        base += 64;
      }
      return true;
    }
  };
};

#endif
