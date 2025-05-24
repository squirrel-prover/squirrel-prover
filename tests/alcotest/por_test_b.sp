(* A conflict should be detected. *)
mutable s (i:index) : bool = true
system Test = !_j !_i s(i) := false.
