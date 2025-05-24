(* No conflict should be detected. *)
mutable s (i:index) : bool = true
system Test = !_i s(i) := false.
