(* Check conflict detection with multiupdates. *)
(* A conflict must be found: we have concurrent writes
   on same projection. *)

mutable s (i,j:index) : message = empty
mutable t (i,j:index) : message = empty
mutable u (i:index) : message = empty

system Test =
  (!_i !_j diff(s i j, t i j) := empty) |
  (!_i diff(s i i,u i) := empty).
