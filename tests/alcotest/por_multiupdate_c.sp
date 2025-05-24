(* Check conflict detection with multiupdates. *)
(* No conflict should be found: the conflict found in test b is protected
   by the mutex added here.
   The conflict is on the left when i=j in first subprocess
   and the i indices of the two !_i are identical.
   We protect it as "lightly" as possible with a mutex on the right
   on j in first subprocess and i in second one. *)

mutable s (i,j:index) : message = empty
mutable t (i,j:index) : message = empty
mutable u (i:index) : message = empty

mutex m : 1

system Test =
  (!_i !_j lock m(j); diff(s i j, t i j) := empty; unlock m(j)) |
  (!_i lock m(i); diff(s i i,u i) := empty; unlock m(i)).
