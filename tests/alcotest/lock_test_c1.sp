(* A conflict should be detected. *)
mutable s (i:index) : bool = true
mutex m : 1
system Test = !_i !_j (lock m(j); s(i) := false; unlock m(j)).
