(* Conflict analysis with multilocks but single cells. *)
(* Here a conflict should be detected: there is a lock m owned on the left
   that is owned on the right, but that is not enough to avoid the
   write/write conflict. *)
mutable s : bool = true
mutex m: 0
mutex dummy_l : 0
mutex dummy_r : 0
system Test = (
    (lock diff(m,dummy_r);
     s := false;
     unlock diff(m,dummy_r))
  | (lock diff(dummy_l,m);
     s := false;
     unlock diff(dummy_l,m))
).
