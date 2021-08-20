#ifndef __GEAS_BIT_MAP_H__
#define __GEAS_BIT_MAP_H__
// Implementation of a crit-bit tree/binary trie a la DJB.

#include <boost/optional.hpp>

class uint_to_bytes {
public:
  static size_t size = sizeof(unsigned int);  
  static void ToBytes(unsigned int x, unsigned char* b) {
    int* uint_b = (int*) b;
    *b = x;
  }
};

class int_to_bytes {
public:
  static size_t size = sizeof(int);
  static int mask = 1<<((8*sizeof(int))-1);
  static void to_bytes(int x, unsigned char* b) {
    int* uint_b = (int*) b;
    *b = x^mask;
  }
};

template<class Key, class ToBytes, class Value>
class BitMap {
public:
  typedef Key K;
  typedef Value V;
  typedef unsigned char bytes_t[ToBytes::size];

  typedef struct node_t {
    node* children[2]; 
    unsigned int byte_num : 23;
    unsigned char is_leaf : 1;
    unsigned char mask;
  } node_t ;

  typedef struct {
    K key;
    bytes_t bytes; 
    V val;
  } elt;

  BitMap(void) { }
     
  optional<V> find(Key& k) const {
    if(!root)
      return;
    
    bytes_t key_bytes;
    ToBytes::to_bytes(k, key_bytes);

    elt* n(search(root, key_bytes));
    assert(n);
     
  }

  void add(Key& k, V& val)
  {
     
  }
protected:
  node_t* search(bytes_t bytes, node_t* root)
  {

  }

  vec<elt> elts;
};

#endif
