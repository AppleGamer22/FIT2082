#ifndef __SPARSE_SET_H__
#define __SPARSE_SET_H__

#include <cassert>
#include <cstdlib>

class SparseSet {
public:
   SparseSet(void) : dom(0), sparse(NULL), dense(NULL), members( 0 )
   {

   }

   SparseSet(unsigned int size) : dom(size),
      sparse((unsigned int*) malloc(size*sizeof(unsigned int))),
      dense((unsigned int*) malloc(size*sizeof(unsigned int))),
      members( 0 )
   {

   }

   ~SparseSet() {
      if( sparse )
         free(sparse);
      if( dense )
         free(dense);  
   }

   bool elem(unsigned int value) const {
     unsigned int a = sparse[value];

     if( a < members && dense[a] == value )
        return true;
     return false;
   }
   
   bool elemLim(unsigned int lim, unsigned int el)
   {
      return (sparse[el] < lim) && elem(el);
   }

   bool insert(unsigned int value)
   {
      assert( !elem(value) );

      sparse[value] = members;
      dense[members] = value;
      members++;
      
      return true;
   }

   void remove(unsigned int value)
   {
     if(!elem(value))
       return;

     unsigned int pos = sparse[value];

     members--;
     unsigned int replacement = dense[members];
     sparse[replacement] = pos;
     dense[pos] = replacement;
   }
   
   void clear(void) {
      members = 0;
   }

   unsigned int pos(unsigned int val) const
   {
      assert( elem(val) );
      return sparse[val];
   }
    
   unsigned int operator [] (unsigned int index) {
      assert(index < members);
      return dense[index];
   }
    
   void growTo(unsigned int sz)
   {
      if( sz > dom )
      {
         sparse = (unsigned int*) realloc(sparse,sizeof(unsigned int)*sz); 
         dense = (unsigned int*) realloc(dense,sizeof(unsigned int)*sz);
      }
   }

   unsigned int size(void) {
      return members;
   }
   
   unsigned int domain(void) {
      return dom;
   }
       
protected:
   unsigned int dom;
   unsigned int* sparse;
   unsigned int* dense;
   unsigned int members;
};

#endif
