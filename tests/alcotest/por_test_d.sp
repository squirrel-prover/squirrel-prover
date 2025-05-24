(* A conflict should be detected. *)
mutable s (i:index) : bool = true
abstract i : index
system Test = (s(i) := false | !_j if s(j) then null).
