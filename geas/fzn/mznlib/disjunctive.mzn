%predicate fzn_disjunctive_var(array[int] of var int: s,
%  array[int] of var int: d);
predicate fzn_disjunctive(array[int] of var int: s,
  array[int] of int: d);

%predicate disjunctive(array[int] of var int: s, array[int] of var int: d) =
%    fzn_disjunctive_var(s, d, r, b);

predicate disjunctive(array[int] of var int: s, array[int] of int: d) =
  fzn_disjunctive(s, d);
