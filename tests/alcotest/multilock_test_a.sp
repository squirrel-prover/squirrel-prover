(* Conflict analysis with multilocks but single cells. *)
(* Here a conflict should be detected:
   the write/write conflict is protected by the right projection mutexes,
   but protection is insufficient on the left. *)
mutable s (i:index) : bool = true
mutex m : 1
mutex dummy : 2
system Test =
  !_j !_i (
    lock diff(dummy(i,j),m(i));
    s(i) := false;
    unlock diff(dummy(i,j),m(i))
  ).
