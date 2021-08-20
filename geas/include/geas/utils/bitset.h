#ifndef GEAS__SPARSE_BITSET__H
#define GEAS__SPARSE_BITSET__H
#include <geas/mtl/p-sparse-set.h>
#include <geas/solver/solver_data.h>

// Standard bitset.
namespace btset {

  typedef uint64_t word_ty;
  typedef unsigned int idx_ty;
  inline size_t word_bits(void) { return 8 * sizeof(word_ty); }
  inline size_t req_words(unsigned int sz) { return (sz + word_bits() - 1)/word_bits(); }

  inline idx_ty elt_idx(unsigned int e) { return e / word_bits(); }
  inline idx_ty elt_bit(unsigned int e) { return e % word_bits(); }
  inline word_ty elt_mask(unsigned int e) { return ((word_ty) 1)<<elt_bit(e); }


  // Standard bit-set. Not really suitable for iteration.
  class bitset {
    bitset(const bitset& o)
      : cap(0), mem(nullptr) { }
    bitset& operator=(const bitset& o) { return *this; }
  public:
    bitset(unsigned int sz)
      : cap(req_words(sz)), mem((word_ty*) malloc(sizeof(word_ty) * req_words(sz))) {
      memset(mem, 0, sizeof(word_ty) * cap);
    }
    bitset(bitset&& o)
      : cap(o.cap), mem(o.mem) {
        o.cap = 0;
        o.mem = nullptr;
      }
    ~bitset(void) {
      if(mem)
        free(mem);
    }
  
    bool elem(unsigned int e) const { return mem[elt_idx(e)] & elt_mask(e); }
    void insert(unsigned int e) { mem[elt_idx(e)] |= elt_mask(e); }
    bool is_empty(void) const {
      for(size_t ii = 0; ii < cap; ++ii) {
        if(mem[ii])
          return false;
      }
      return true;
    }

    void fill(size_t sz) {
      assert(req_words(sz) <= cap);
      // Fill the array with 1s
      memset(mem, (char) -1, sizeof(word_ty) * req_words(sz));
      if(elt_bit(sz))
        mem[req_words(sz)-1] &= (elt_mask(sz)-1);
    }
    /*
    void clear(void) { memset(mem, 0, sizeof(word_ty) * sz); }
    void insert(unsigned int e) { mem[elt_idx(e)] |= elt_mask(e); }
    void remove(unsigned int e) { mem[elt_idx(e)] &= ~elt_mask(e); }

    void union_with(const bitset& o) {
      for(size_t ii = 0; ii < sz; ++ii)
        mem[ii] |= o.mem[ii];
    }
    void intersect_with(const bitset& o) {
      for(size_t ii = 0; ii < sz; ++ii)
        mem[ii] &= o.mem[ii];
    }
    */
    word_ty& operator[](unsigned int w) const { return mem[w]; }

    word_ty get_word(unsigned int w) const { return mem[w]; }
    size_t num_words(void) const { return cap; }
    size_t size(void) const { return cap; }
  protected:
    size_t cap;
    word_ty* mem;
  };

  // For when we have a static, sparse set of
  // items (like supports, or transition relations)
  struct support_set {
    struct elem_ty {
      idx_ty w;
      word_ty bits;
    };

    template<class It>
    static size_t idx_sz(It b, It e) {
      if(b != e) {
        size_t c = 1;
        unsigned int w(elt_idx(*b));
        for(++b; b != e; ++b) {
          if(elt_idx(*b) != w) {
            w = elt_idx(*b);
            ++c;
          }
        }
        return c;
      } else {
        return 0;
      }
    }

    template<class It>
    static size_t mem_sz(It b, It e) {
      return (b != e) ? req_words(1 + *std::max_element(b, e)) : 0;
    }

    template<class It>
    support_set(It b, It e)
      : sz(idx_sz(b, e))
      , mem((elem_ty*) malloc(sizeof(elem_ty) * mem_sz(b, e))) {
      if(b != e) {
        elem_ty* ptr(mem);
        (*ptr) = elem_ty { elt_idx(*b), elt_mask(*b) }; 

        for(++b; b != e; ++b) {
          if(elt_idx(*b) != ptr->w) {
            ++ptr;
            (*ptr) = elem_ty { elt_idx(*b), elt_mask(*b) };
          } else {
            ptr->bits |= elt_mask(*b);
          }
        }
      }
    }

    template<class V>
    static support_set make(const V& v) { return support_set(v.begin(), v.end()); }

    elem_ty* begin(void) const { return mem; }
    elem_ty* end(void) const { return mem+sz; } 
    unsigned int size(void) const { return sz; }

    elem_ty& operator[](unsigned int p) const { return mem[p]; }

    unsigned int sz;
    elem_ty* mem;
  };


  class p_sparse_bitset {
  public:
    p_sparse_bitset(unsigned int _cap)
      : cap(req_words(_cap))
      , mem((word_ty*) malloc(sizeof(word_ty) * cap))
      , idx(cap) {
      // Don't need to initialize mem.
    }

    p_sparse_bitset(p_sparse_bitset&& o)
      : cap(o.cap)
      , mem(o.mem)
      , idx(std::move(o.idx)) {
        o.cap = 0;
        o.mem = nullptr;
    }

    void swap(p_sparse_bitset& o) {
      std::swap(cap, o.cap);
      std::swap(mem, o.mem);
      std::swap(idx, o.idx);
    }

    ~p_sparse_bitset(void) {
      if(mem)
        free(mem);
    }

    void growTo(unsigned int sz) {
      size_t new_cap(req_words(sz));
      if(cap < new_cap) {
        idx.growTo(new_cap);
        mem = (word_ty*) realloc(mem, sizeof(word_ty) * new_cap);
        cap = new_cap;
      }
    }

    void clear(void) { idx.clear(); }
    bool elem(unsigned int e) const {
      if(!idx.elem(elt_idx(e))) return false;
      return mem[elt_idx(e)] & elt_mask(e);
    }
    bool is_empty(void) const { return idx.size() == 0; }

    void insert(unsigned int e) {
      if(!idx.elem(elt_idx(e))) {
        idx.insert(elt_idx(e));
        mem[elt_idx(e)] = elt_mask(e);
      } else {
        mem[elt_idx(e)] |= elt_mask(e);
      }
    }
    void remove(unsigned int e) {
      unsigned int w(elt_idx(e));
      if(!idx.elem(w))
        return;
      if(mem[w] & ~elt_mask(e))
        mem[w] &= ~elt_mask(e);
      else
        idx.remove(w);
    }

    void fill(size_t sz) {
      assert(req_words(sz) <= cap);
      if(req_words(sz) == cap)
        idx.sz = cap;
      else {
        idx.clear();
        for(int ii = 0; ii < req_words(sz); ++ii)
          idx.insert(ii);
      }
      // Fill the array with 1s
      memset(mem, (char) -1, sizeof(word_ty) * req_words(sz));
      if(elt_bit(sz))
        mem[req_words(sz)-1] &= (elt_mask(sz)-1);
    }
    
    void init(const support_set& ss) {
      idx.clear();
      for(auto e : ss) {
        idx.insert(e.w);
        mem[e.w] = e.bits; 
      }
    }

    void union_with(const support_set& o) {
      for(auto e : o) {
        if(!idx.elem(e.w)) {
          idx.insert(e.w);
          mem[e.w] = e.bits;
        } else {
          mem[e.w] |= e.bits;
        }
      }
    }

    void remove(const support_set& o) {
      for(auto e : o) {
        if(idx.elem(e.w)) {
          word_ty bits(mem[e.w] & ~e.bits);
          if(!bits)
            idx.remove(e.w);
          mem[e.w] = bits;
        }
      }
    }

    bool has_intersection(const support_set& o) const {
      for(auto e : o) {
        if(!idx.elem(e.w))
          continue;
        if(mem[e.w] & e.bits)
          return true;
      }
      return false;
    }

    void set(const support_set& o) {
      idx.clear();
      for(auto e : o) {
        idx.insert(e.w);
        mem[e.w] = e.bits; 
      }
    }
    void set(const p_sparse_bitset& o) {
      idx.clear();
      for(int w : o.idx) {
        idx.insert(w);
        mem[w] = o.mem[w];
      }
    }

    void intersect_with(const p_sparse_bitset& o) {
      // Reverse order, since we'll be swapping things
      // to the end.
      for(int p = idx.size()-1; p >= 0; --p) {
        unsigned int w(idx[p]);
        if(!o.idx.elem(w)) {
          idx.remove(w);
          continue;
        }
        word_ty m(mem[w] & o.mem[w]);
        mem[w] = m;
        if(!m) {
          idx.remove(w);
        }
      }
    }

    // TODO: Check which index is smaller, and use that.
    void remove(const p_sparse_bitset& o) {
      for(int p = idx.size()-1; p >= 0; --p) {
        unsigned int w(idx[p]);
        if(!o.idx.elem(w))
          continue;  
        word_ty m(mem[w] & ~o.mem[w]);
        mem[w] = m;
        if(!m) {
          idx.remove(w);
        }
      }
    }

    bool has_intersection(const p_sparse_bitset& o) const {
      if(o.idx.size() < idx.size())
        return o.has_intersection(*this);
      for(unsigned int w : idx) {
        if(o.idx.elem(w) && (mem[w] & o.mem[w]))
          return true;
      }
      return false;
    }

    word_ty& operator[](unsigned int w) {
      return mem[w];
    }

    void intersect_word(unsigned int w, word_ty wd) {
      if(mem[w] & ~wd) {
        mem[w] &= ~wd;
      } else {
        idx.remove(w);
      }
    }

    inline void remove_word(unsigned int w, word_ty wd) {
      intersect_word(w, ~wd);
    }
     
    word_ty get_word(unsigned int w) {
      assert(idx.elem(w));
      return mem[w];
    }

    unsigned int num_words(void) const { return cap; }

    size_t cap;
    word_ty* mem;
    p_sparseset idx;
  };

};

namespace std {
  using namespace btset;
  inline void swap(p_sparse_bitset& x, p_sparse_bitset& y) { return x.swap(y); }
};


#endif
