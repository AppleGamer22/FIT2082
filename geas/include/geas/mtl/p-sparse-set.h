#ifndef __PERM_SPARSE_SET_H__
#define __PERM_SPARSE_SET_H__

#include <cassert>
#include <cstdlib>

// Variant of sparse set, which preserves sparse as a permutation
// of 1..n.
// Cheaper lookups, slightly more expensive modifications

class p_sparseset {
  enum { dom_default = 10 };
public:
   p_sparseset(void)
     : dom(dom_default),
       sz( 0 ),
       sparse((unsigned int*) malloc(dom*sizeof(unsigned int))),
       dense((unsigned int*) malloc(dom*sizeof(unsigned int)))
   {
      for(unsigned int ii = 0; ii < dom; ii++) {
        sparse[ii] = ii;
        dense[ii] = ii;
      }
   }

   p_sparseset(unsigned int size) : dom(size),
      sz( 0 ),
      sparse((unsigned int*) malloc(std::max(1u, size)*sizeof(unsigned int))),
      dense((unsigned int*) malloc(std::max(1u, size)*sizeof(unsigned int)))
   {
      for(unsigned int ii = 0; ii < dom; ii++) {
        sparse[ii] = ii;
        dense[ii] = ii;
      }
   }

   p_sparseset(p_sparseset&& o)
    : dom(o.dom), sz(o.sz), sparse(o.sparse), dense(o.dense) {
      o.dom = 0;
      o.sz = 0;
      o.sparse = nullptr;
      o.dense = nullptr;
    }

   ~p_sparseset() {
      if( sparse )
         free(sparse);
      if( dense )
         free(dense);  
   }

   void swap(p_sparseset& o) {
     std::swap(sz, o.sz);
     std::swap(sparse, o.sparse);
     std::swap(dense, o.dense);
   }

   struct range {
     unsigned int* begin(void) const { return s; }
     unsigned int* end(void) const { return e; }

     unsigned int* s;
     unsigned int* e;
   };
   unsigned int* begin(void) const { return dense; }
   unsigned int* end(void) const { return dense+sz; }
   
   struct riter {
     unsigned int operator*(void) const { return *p; }
     bool operator!=(const riter& o) const { return p != o.p; }
     riter operator++(void) { --p; return *this; }

     unsigned int* p;
   };

   struct rrange {
     riter begin(void) const { return riter {e-1}; };
     riter end(void) const { return riter {b-1}; }

    unsigned int* b;
    unsigned int* e; 
   };

   // Iterate over elements _not_ in the set.
   range complement(void) const { return range { dense+sz, dense+dom }; }
   range slice(unsigned int b, unsigned int e) { return range { dense+b, dense+e }; }
   range all_values(void) const { return range { dense, dense+dom }; }

   rrange rev(void) const { return rrange { dense, dense+sz }; }

   inline bool elem(unsigned int value) const {
     return sparse[value] < sz;
   }
   
   bool insert(unsigned int value) {
//      assert( !elem(value) );

      unsigned int repl = dense[sz];
      unsigned int r_idx = sparse[value];

      dense[r_idx] = repl;
      sparse[repl] = r_idx;

      sparse[value] = sz;
      dense[sz] = value;
      sz++;
      
      return true;
   }

   void remove(unsigned int value) {
//     if(!elem(value))
//       return;
     unsigned int pos = sparse[value];

     sz--;
     unsigned int replacement = dense[sz];

     sparse[replacement] = pos;
     dense[pos] = replacement;

     sparse[value] = sz;
     dense[sz] = value;
   }
   
   void clear(void) {
      sz = 0;
   }

   unsigned int pos(unsigned int val) const
   {
      // assert( elem(val) );
      return sparse[val];
   }
    
   unsigned int operator [] (unsigned int index) const {
      assert(index < dom);
      return dense[index];
   }
    
   void growTo(unsigned int new_dom)
   {
      if( dom <= new_dom )
      {
        unsigned int old_dom = dom;
        dom = std::max(dom, 2u);
        while(dom <= new_dom)
          dom *= 1.5;
        // Of course, this is bad practice -- should check the return value
        sparse = (unsigned int*) realloc(sparse,sizeof(unsigned int)*dom); 
        dense = (unsigned int*) realloc(dense,sizeof(unsigned int)*dom);

        // Initialize the newly added elements
        for(; old_dom < dom; old_dom++) {
          sparse[old_dom] = old_dom;
          dense[old_dom] = old_dom;
        }
      }
   }

   void growTo_strict(unsigned int new_dom)
   {
      if( dom <= new_dom )
      {
        /*
        unsigned int old_dom = dom;
        while(dom <= new_dom)
          dom *= 1.5;
          */
        unsigned int old_dom = dom;
        dom = new_dom;
        // Of course, this is bad practice -- should check the return value
        sparse = (unsigned int*) realloc(sparse,sizeof(unsigned int)*dom); 
        dense = (unsigned int*) realloc(dense,sizeof(unsigned int)*dom);

        // Initialize the newly added elements
        for(; old_dom < dom; old_dom++) {
          sparse[old_dom] = old_dom;
          dense[old_dom] = old_dom;
        }
      }
   }

   unsigned int size(void) const {
      return sz;
   }
   
   unsigned int domain(void) const {
      return dom;
   }
       
   unsigned int dom;
   unsigned int sz;
protected:
   unsigned int* sparse;
   unsigned int* dense;
};

namespace std {
  inline void swap(p_sparseset& x, p_sparseset& y) { return x.swap(y); }
};

#endif
