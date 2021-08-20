#ifndef __GREYLIB_BIT_TRIEMAP_H__
#define __GREYLIB_BIT_TRIEMAP_H__
#include <cstdlib>
#include <cassert>
#include <geas/utils/cast.h>
#include <geas/mtl/bit-flag.h>

class UIntOps {
public:
  static uint64_t to_uint(uint64_t t) { return t; }
  static uint64_t from_uint(uint64_t t) { return t; }
};

class IntOps {
public:
  enum { mask = 1<<31 };
  static unsigned int to_uint(int t) { return ((unsigned int) t)^mask; }
  static int from_uint(unsigned int t) { return (int) (t^mask); }
};

class FloatOps {
  enum { mask = 1<<31 };
public:
  static unsigned int to_uint(float t)
  {
    int t_int = cast::conv<int, float>(t);
//    int t_int = *(reinterpret_cast<int*>(&t));
    if(t_int < 0)
      t_int = 0x80000000 - t_int;
    return mask^(t_int);
  }

  static float from_uint(unsigned int t)
  {
    int t_int = (int) (t^mask);
    if(t_int < 0)
      t_int = 0x80000000 - t_int;
    // return *(reinterpret_cast<float*>(&t_int));
    return cast::conv<float, int>(t_int);
  }
};

template<class Key, class Val, class Ops>
class uint64_triemap {
  typedef uint64_t elt_t;
private:
  uint64_triemap(uint64_triemap<Key, Val, Ops>& o)
    : root(nullptr) { }
  uint64_triemap& operator=(uint64_triemap<Key,Val,Ops>& o) {
    return *this;
  }
protected:
  // Internal and leaf nodes
  typedef struct {
    uint64_t mask;
    void* left;
    void* right;
  } node_t;

public:
  class ref_t {
  public:
    ref_t(const Key& _key, const Val& _val)
      : key(_key), value(_val)
    { }
    Key key;
    Val value;
  };

  class leaf_t {
  public:
    leaf_t(const Key& _elt, const Val& _val, leaf_t* _prev, leaf_t* _next)
      : ref(_elt, _val), prev(_prev), next(_next)
    { }
    ref_t ref;
    leaf_t* prev;
    leaf_t* next;
  };

  class iterator {
  public:
    iterator(leaf_t* _l)
      : l(_l)
    { } 

    iterator& operator++(void) {
      l = l->next; return *this;
    }
    iterator& operator--(void) {
      l = l->prev; return *this;
    }
    ref_t& operator*(void) const {
      return l->ref;
    }
    bool operator!=(const iterator& o) const {
      return l != o.l;
    }
    operator bool() {
      return l != NULL;
    }
  protected:
    leaf_t* l;
  };

  uint64_triemap(void)
    : root(NULL), head(NULL), tail(NULL)
  { } 

  uint64_triemap(uint64_triemap<Key, Val, Ops>&& o)
    : root(o.root), head(o.head), tail(o.tail) {
      o.root = nullptr;
      o.head = o.tail = nullptr;
  }

  uint64_triemap& operator=(uint64_triemap<Key, Val, Ops>&& o) {
    root = o.root; o.root = nullptr;
    head = o.head; o.head = nullptr;
    tail = o.tail; o.tail = nullptr;
    return *this;
  }

  ~uint64_triemap()
  {
    if(root)
      free_node(root);
  }

  iterator add(const Key& key, const Val& v) {
    if(!root)
    {
      root = make_leaf(key, v, NULL, NULL);
      head = tail = (leaf_t*) root;
      return head;
    }

    elt_t e = Ops::to_uint(key);
    leaf_t* leaf = locate(e);

    // Already in the set
    if(leaf->ref.key == key)
    {
      leaf->ref.value = v;
      return leaf;
    }

//    unsigned int mask = get_mask(e^(leaf->ref.key));
    uint64_t mask = get_mask(e^Ops::to_uint(leaf->ref.key));
    uint64_t out_dir = e&mask;
    
    void** p = NULL;
    void* node = root;
    node_t* node_ptr = clear_flag((node_t*) node);
    while(check_flag(node) &&
        node_ptr->mask > mask)
    {
      uint64_t dir = e&node_ptr->mask;
      p = dir ? &(node_ptr->right) : &(node_ptr->left);
      node = dir ? node_ptr->right : node_ptr->left;
      node_ptr = clear_flag((node_t*) node);
    }
    
    leaf_t* prev;
    leaf_t* next; 
    if(out_dir)
    {
      void* adj_node = node;
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->right;
      }
      prev = ((leaf_t*) adj_node);
      next = prev->next;
    } else {
      void* adj_node = node; 
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->left;
      }
      next = ((leaf_t*) adj_node);
      prev = next->prev;
    }
    leaf_t* fresh_leaf = new leaf_t(key, v, prev, next);

    // Fix up the linked list
    if(fresh_leaf->prev)
      fresh_leaf->prev->next = fresh_leaf;
    if(fresh_leaf->next)
      fresh_leaf->next->prev = fresh_leaf;

    if(head == next)
      head = fresh_leaf;
    if(tail == prev)
      tail = fresh_leaf;

    void* fresh_node = make_node(mask,
      out_dir ? node : (void*) fresh_leaf,
      out_dir ? (void*) fresh_leaf : node);
    if(p == NULL)
      root = fresh_node;
    else
      (*p) = fresh_node;

    return fresh_leaf;
  }

  template<class Construct>
  Val find_or_add(Construct& construct, const Key& key) {
    if(!root)
    {
      root = make_leaf(key, construct(key), NULL, NULL);
      head = tail = (leaf_t*) root;
      return head->ref.value;
    }

    elt_t e = Ops::to_uint(key);
    leaf_t* leaf = locate(e);

    // Already in the set
    if(leaf->ref.key == key)
    {
      return leaf->ref.value;
    }

    uint64_t mask = get_mask(e^Ops::to_uint(leaf->ref.key));
    uint64_t out_dir = e&mask;
    
    void** p = NULL;
    void* node = root;
    node_t* node_ptr = clear_flag((node_t*) node);
    while(check_flag(node) &&
        node_ptr->mask > mask)
    {
      uint64_t dir = e&node_ptr->mask;
      p = dir ? &(node_ptr->right) : &(node_ptr->left);
      node = dir ? node_ptr->right : node_ptr->left;
      node_ptr = clear_flag((node_t*) node);
    }
    
    leaf_t* prev;
    leaf_t* next; 
    if(out_dir)
    {
      void* adj_node = node;
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->right;
      }
      prev = ((leaf_t*) adj_node);
      next = prev->next;
    } else {
      void* adj_node = node; 
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->left;
      }
      next = ((leaf_t*) adj_node);
      prev = next->prev;
    }
    leaf_t* fresh_leaf = new leaf_t(key, construct(prev->ref.value, key), prev, next);

    // Fix up the linked list
    if(fresh_leaf->prev)
      fresh_leaf->prev->next = fresh_leaf;
    if(fresh_leaf->next)
      fresh_leaf->next->prev = fresh_leaf;

    if(head == next)
      head = fresh_leaf;
    if(tail == prev)
      tail = fresh_leaf;

    void* fresh_node = make_node(mask,
      out_dir ? node : (void*) fresh_leaf,
      out_dir ? (void*) fresh_leaf : node);
    if(p == NULL)
      root = fresh_node;
    else
      (*p) = fresh_node;

    return fresh_leaf->ref.value;
  }

  iterator lower_bound(const Key& key) {
    if(root == NULL)
      return NULL;

    elt_t e = Ops::to_uint(key);
    leaf_t* leaf = locate(e);

    // Exact value present.
    if(leaf->ref.key == key)
    {
      return leaf;
    }

    uint64_t mask = get_mask(e^Ops::to_uint(leaf->ref.key));
    uint64_t out_dir = e&mask;
    
    // void** p = NULL;
    void* node = root;
    node_t* node_ptr = clear_flag((node_t*) node);
    while(check_flag(node) &&
        node_ptr->mask > mask)
    {
      uint64_t dir = e&node_ptr->mask;
      // p = dir ? &(node_ptr->right) : &(node_ptr->left);
      node = dir ? node_ptr->right : node_ptr->left;
      node_ptr = clear_flag((node_t*) node);
    }
    
    if(out_dir)
    {
      void* adj_node = node;
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->right;
      }
      return ((leaf_t*) adj_node)->next;
    } else {
      void* adj_node = node; 
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->left;
      }
      return ((leaf_t*) adj_node);
    }
  }

  iterator upper_bound(const Key& key) {
    if(root == NULL)
      return NULL;

    elt_t e = Ops::to_uint(key);
    leaf_t* leaf = locate(e);

    // Exact value present.
    if(leaf->ref.key == key)
    {
      return leaf->next;
    }

    uint64_t mask = get_mask(e^Ops::to_uint(leaf->ref.key));
    uint64_t out_dir = e&mask;
    
    // void** p = NULL;
    void* node = root;
    node_t* node_ptr = clear_flag((node_t*) node);
    while(check_flag(node) &&
        node_ptr->mask > mask)
    {
      uint64_t dir = e&node_ptr->mask;
      // p = dir ? &(node_ptr->right) : &(node_ptr->left);
      node = dir ? node_ptr->right : node_ptr->left;
      node_ptr = clear_flag((node_t*) node);
    }
    
    if(out_dir)
    {
      void* adj_node = node;
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->right;
      }
      return ((leaf_t*) adj_node)->next;
    } else {
      void* adj_node = node; 
      while(check_flag(adj_node))
      {
        adj_node = clear_flag((node_t*) adj_node)->left;
      }
      return ((leaf_t*) adj_node);
    }
  }


  void rem(elt_t e)
  {
    if(root == NULL)
      return;

    void* p = root;
    node_t* q = NULL;

    void** whereq = NULL;
    void** wherep = &(root);
    uint64_t dir;

    while(check_flag(p))
    {
      whereq = wherep;
      q = clear_flag((node_t*) p);
      dir = e&(q->mask);
      wherep = dir ? &(q->right) : &(q->left);
      p = *wherep;
    }

    // If value not in the trie, terminate
    leaf_t* leaf((leaf_t*) p);
    if(e != leaf->ref.key)
      return;
    
    // Disconnect the leaf, then free it.
    if(leaf->prev)
    {
      leaf->prev->next = leaf->next;
    } else {
      head = leaf->next;
    }
    if(leaf->next)
    {
      leaf->next->prev = leaf->prev;
    } else {
      tail = leaf->prev;
    }
    delete leaf;

    // Collapse the last decision.
    if(!whereq)
    {
      root = NULL;
      return;
    }
    (*whereq) = dir ? q->left : q->right;
    delete q;
  }

  bool mem(elt_t e) {
    if(root == NULL)
      return false;

    leaf_t* leaf = locate(e);
    return (e == leaf->elt);
  }

  iterator find(const elt_t& e) const {
    if(root == NULL)
      return NULL;

    leaf_t* leaf = locate(e);
    return (e == leaf->ref.key) ? leaf : NULL;
  }

  iterator begin(void) const { return head; }
  iterator end(void) const { return NULL; }
protected:
  void free_node(void* ptr)
  {
    if(check_flag(ptr))
    {
      node_t* node_ptr(clear_flag((node_t*) ptr));
      free_node(node_ptr->left);
      free_node(node_ptr->right);
      delete node_ptr;
    } else {
      leaf_t* leaf_ptr((leaf_t*) ptr);
      delete leaf_ptr;
    }
  }
  void* make_node(uint64_t mask, void* left, void* right)
  {
    node_t* ptr = new node_t;
    ptr->mask = mask;
    ptr->left = left;
    ptr->right = right;
    
    return set_flag(ptr);
  }

  void* make_leaf(elt_t e, const Val& v, leaf_t* prev, leaf_t* next)
  {
    return (void*) (new leaf_t(e, v, prev, next));
  }

  // Extract the most significant 1-bit
  uint64_t get_mask(uint64_t x)
  {
    // Alternatively, use bit-smearing.
    // return (1<<(31-__builtin_clz(x)));
    static_assert(sizeof(uint64_t) == sizeof(unsigned long long),
      "uint64_trie: compiler intrinsic for wrong bit-width");
    return ((uint64_t) 1)<<(63-__builtin_clzll(x));
  }

  // Find the leaf where [elt] would reside
  leaf_t* locate(const elt_t& elt) const
  {
    if(root == NULL)
      return NULL;

    void* ptr = root;
    // While we're at an internal node
    while(check_flag(ptr))
    {
      node_t* node = clear_flag((node_t*) ptr);
      uint64_t dir = elt&node->mask;
      ptr = dir ? node->right : node->left;
    }
    return (leaf_t*) ptr;
  }

  void* root;
public:
  leaf_t* head;
  leaf_t* tail;
};

/*
template<class V>
class int_triemap {
  enum { mask = 1<<31 };
public:
  int_triemap( )
  { }

  void add(int t) { impl.add(((unsigned int)t)^mask); }
  bool find(int t) { return impl.find(((unsigned int) t)^mask); }
  void rem(int t) { impl.rem(((unsigned int) t)^mask); }
   
  class iterator {
  public:
    iterator(uint_trie::iterator _it)
      : it(_it)
    { }

    iterator& operator++() {
      ++it; return *this;
    }
    int operator*() const { return (*it)^mask; }
    bool operator!=(const iterator& other)
    { return it != other.it; }
  protected:
    uint_trie::iterator it;
  };
  iterator begin() { return iterator(impl.begin()); }
  iterator end() { return iterator(impl.end()); }
protected:
  uint_trie impl;
};

class float_trie {
//  enum { mask = 3<<30 };
  enum { mask = 1<<31 };
  
  static unsigned int to_uint(float t)
  {
    int t_int = *(reinterpret_cast<int*>(&t));
    if(t_int < 0)
      t_int = 0x80000000 - t_int;
    return mask^(t_int);
  }

  static float from_uint(unsigned int t)
  {
    int t_int = (int) (t^mask);
    if(t_int < 0)
      t_int = 0x80000000 - t_int;
    return *(reinterpret_cast<float*>(&t_int));
  }
public:
  float_trie( )
  { }

  void add(float t) { impl.add(to_uint(t)); }
  bool find(float t) { return impl.find(to_uint(t)); }
  void rem(float t) { impl.rem(to_uint(t)); }
   
  class iterator {
  public:
    iterator(uint_trie::iterator _it)
      : it(_it)
    { }

    iterator& operator++() {
      ++it; return *this;
    }
    float operator*() const { return from_uint((*it)); }
    bool operator!=(const iterator& other)
    { return it != other.it; }
  protected:
    uint_trie::iterator it;
  };
  iterator begin() { return iterator(impl.begin()); }
  iterator end() { return iterator(impl.end()); }
protected:
  uint_trie impl;
};
*/

#endif
