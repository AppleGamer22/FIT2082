predicate fzn_cumulative_var(array[int] of var int: s,
  array[int] of var int: d,
  array[int] of var int: r,
  var int: b);
predicate fzn_cumulative(array[int] of var int: s,
  array[int] of int: d,
  array[int] of int: r,
  int: b);


predicate cumulative(array[int] of var int: s,
  array[int] of var int: d,
  array[int] of var int: r,
  var int: b) =
    fzn_cumulative_var(s, d, r, b);

%% TODO: once disjunctive propagator is fixed, add
%% special case for b = 1.
predicate cumulative(array[int] of var int: s,
  array[int] of int: d,
  array[int] of int: r,
  int: b) =
    fzn_cumulative(s, d, r, b);
