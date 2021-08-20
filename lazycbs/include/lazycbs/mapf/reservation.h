#ifndef GMAPF__RESERVATION__H
#define GMAPF__RESERVATION__H
#include <geas/engine/persist.h>
// For strong branching, we want two sorts of reservation tables; for each
// <loc, time>, we need to be able to track:
// - Which (if any) agent is it reserved for, and
// - Which agents would _like_ to reserve it (have a candidate path through the location).
/*
struct reservation {
  enum { BLOCK_SZ = 4 };

  unsigned int block(int r, int c, int t) {
    return Cblocks * ( Rblocks * (t / BLOCK_SZ) + (r / BLOCK_SZ))  + (c / BLOCK_SZ);
  }
  unsigned int block_offset(int r, int c, int t) {
    return BLOCK_SZ * (BLOCK_SZ * (t % BLOCK_SZ) + (r % BLOCK_SZ)) + (c % BLOCK_SZ);
  }

  unsigned int Rblocks;
  unsigned int Cblocks;

  struct block {

  };
};
*/
// Not enough to record whether a given loctime is assigned, we also need
// to be able to reconstruct why.
// But! (1) Most of the time, we don't care about the reason, we just need to make
// lookups fast. And (2) for a given agent, the reason is always var_of(loctime) != ai.
// Still need to do allocations in a block structure, because we want trailing to work
// automagically.
// Alternatively, we can do the usual thing of recording changes, which saves us an additional
// indirection on each lookup...

struct reservation {
  static unsigned int BLOCK_MASK(void) { return (1<<6)-1; }
  static uint64_t BLOCK_OF(uint64_t t) { return t>>6; }
  static unsigned int LOC_IDX(uint64_t t) { return t & BLOCK_MASK(); }
  static uint64_t LOC_BIT(uint64_t p) { return 1ull << LOC_IDX(p); }

  struct vars_block {
    geas::intvar xs[64];
  };

  reservation(void) : hist_tl(0) {

  }

  // Requires history to be up to date.
  bool is_reserved(unsigned int t) const {
    unsigned int t_block(BLOCK_OF(t));
    return t_block < assigned.size() && (assigned[t_block] & LOC_BIT(t));
  }

  geas::intvar& reason(unsigned int t) const {
    // Requires time is currently marked as reserved.
    return blocks[BLOCK_OF(t)]->xs[LOC_IDX(t)];
  }

  // Associate loctime t with intvar c_var.
  void record(unsigned int t, geas::intvar c_var) {
    unsigned int t_block(BLOCK_OF(t));
    if(assigned.size() <= t_block) {
      assigned.growTo(t_block+1, 0);
      blocks.growTo(t_block+1, nullptr);
      
      vars_block* b(new vars_block);
      b->xs[LOC_IDX(t)] = c_var;

      blocks[t_block] = b;
    } else if(!blocks[t_block]) {
      vars_block* b(new vars_block);
      b->xs[LOC_IDX(t)] = c_var;

      blocks[t_block] = b;
    } else {
      blocks[t_block]->xs[LOC_IDX(t)] = c_var;
    }
  }

  // Requires allocate(t) has been called previously,
  // and history is up to date.
  template<class P>
  void reserve(P& p, uint64_t t) {
    unsigned int t_block(BLOCK_OF(t));
    unsigned int t_idx(LOC_IDX(t)); 
    uint64_t t_mask(LOC_BIT(t));
    if(!assigned[t_block] & t_mask) {
      assigned[t_block] |= t_mask;
      history.push(t);
      hist_tl.set(p, history.size());
    }
  }
  void restore(void) {
    for(int ii : irange(hist_tl, history.size())) {
      uint64_t p(history[ii]);
      assigned[BLOCK_OF(p)] ^= LOC_BIT(p);
    }
    history.shrink(history.size() - hist_tl);
  }

  vec<uint64_t> assigned;
  vec<vars_block*> blocks;

  vec<uint64_t> history; 
  geas::trailed<unsigned int> hist_tl;
};

#endif
