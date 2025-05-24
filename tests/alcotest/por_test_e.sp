(* Check that read operations are detected inside indices of cells. *)
(* A conflict should be detected. *)
abstract i : index
mutable s : index = i
mutable t (i:index) : bool = true
system Test = (s := i | if t(s) then null).
