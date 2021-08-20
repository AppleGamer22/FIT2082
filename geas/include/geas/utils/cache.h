#ifndef __AUTOCACHE_H__
#define __AUTOCACHE_H__
#include <ext/hash_map>
#include <ext/hash_set>
#include <vector>
//#include <tr1/unordered_map>
#include "MurmurHash3.h"

// Header for automatically generating hash-tables for simple data structures.
//====================================================================
// Limitations: only really works for simple structs, which means no vectors
// or shared-pointers, etc.
#define SEED 0xdeadbeef

template<class S>
struct AutoS
{
  struct eq
  {
    bool operator() (const S& a, const S& b) const
    {
      if(sizeof(S) % sizeof(uint32_t) == 0)
      {
        uint32_t* ap((uint32_t*) &a);
        uint32_t* bp((uint32_t*) &b);
        for(unsigned int ii = 0; ii < sizeof(S)/sizeof(uint32_t); ii++)
        {
          if(ap[ii] != bp[ii])
            return false;
        }
        return true;
      } else {
        char* ap((char*) &a);
        char* bp((char*) &b);
        for(unsigned int ii = 0; ii < sizeof(S); ii++)
        {
          if(ap[ii] != bp[ii])
            return false;
        }
         return true;
      }
    }
  };

  struct hash
  {
    unsigned int operator() (const S& s) const
    {
      uint32_t ret;
      MurmurHash3_x86_32(&s, sizeof(S), SEED, &ret);
      return ret;
    }
  };

  typedef __gnu_cxx::hash_set<S, hash, eq> set;
};

template<class S, class V>
struct AutoC
{
  typedef __gnu_cxx::hash_map<const S, V, typename AutoS<S>::hash, typename AutoS<S>::eq> cache;
//  typedef std::tr1::unordered_map<const S, V, typename AutoS<S>::hash, typename AutoS<S>::eq> cache;
};

struct NilS
{
  struct eq
  {
    bool operator() (const size_t& a, const size_t& b) const
    {
      return a == b;
    }
  };

  struct hash
  {
    unsigned int operator() (const size_t& s) const
    {
      return s;
    }
  };
};

template<class V>
struct NilC
{
  typedef __gnu_cxx::hash_map<const size_t, V, NilS::hash, NilS::eq> cache;
};


#endif
