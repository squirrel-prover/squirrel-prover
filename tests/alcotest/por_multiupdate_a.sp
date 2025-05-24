(* Check conflict detection with multiupdates. *)
(* No conflict should be found: we have concurrent writes
   on s(i,i) and t(i,i) but they are on different projections. *)

mutable s (i,j:index) : message = empty
mutable t (i,j:index) : message = empty

system Test =
  (!_i !_j diff(s i j, t i j) := empty) |
  (!_i !_j diff(t i j, s i j) := empty).
