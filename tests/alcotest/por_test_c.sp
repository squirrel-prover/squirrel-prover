(* A conflict should be detected. *)
mutable s (i:index) : bool = true
system Test = !_i !_j s(i) := false.
