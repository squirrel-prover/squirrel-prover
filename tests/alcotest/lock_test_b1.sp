(* A conflict should be detected. *)
mutable s (i:index) : bool = true
mutex m : 1
system Test = !_j !_i (lock m(j); s(i) := false; unlock m(j)).
