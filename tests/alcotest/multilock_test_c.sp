(* Conflict analysis with multilocks but single cells. *)
(* This file is a variant of multilock_test_b but with replication. *)
(* Here a conflict should be detected: there is a lock m owned on the left
   that is owned on the right, but that is not enough to avoid the
   write/write conflict. *)
mutable s : bool = true
mutex m: 1
mutex dummy_l : 2
mutex dummy_r : 2
system Test = !_i !_j (
    (lock diff(m(i),dummy_r(i,j));
     s := false;
     unlock diff(m(i),dummy_r(i,j)))
  | (lock diff(dummy_l(i,j),m(i));
     s := false;
     unlock diff(dummy_l(i,j),m(i)))
).
