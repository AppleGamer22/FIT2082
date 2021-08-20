#ifndef __GREYLIB_BIT_FLAG_H__
#define __GREYLIB_BIT_FLAG_H__
// Helper functions for dealing with tagged pointers.
#include <stdint.h>
template<class T>
inline void* set_flag(T* ptr)
{ return (void *) (((uintptr_t) ptr)|1); }

template<class T>
inline T* clear_flag(T* ptr)
{ return (T*) (((uintptr_t) ptr)&(~1)); }

template<class T>
inline bool check_flag(T* ptr)
{ return ((uintptr_t) ptr)&1; }
#endif
