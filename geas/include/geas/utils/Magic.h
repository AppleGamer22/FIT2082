#ifndef __GEAS_MAGIC_H__
#define __GEAS_MAGIC_H__
// Magical templatey incantations for stuff.

/*
template<>
class VaArgs
{
public:
  static int val = 0;
}

template<typename T, typename ... Ts>
class VaArgs
{
public:
  static int val = 1 + VaArgs<Ts ...>::val;
}
*/

template<typename T>
inline void get_args(vec<T>& v) { }

template<typename T, typename U, typename ... Ts>
inline void get_args(vec<T>& v, const U& elt, const Ts& ... args)
{
  v.push((T) elt);
  get_args<T, Ts ...>(v, args ...); 
}
#endif
