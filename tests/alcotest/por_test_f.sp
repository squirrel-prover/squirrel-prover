(* Check that read operations are detected inside indices of names. *)
(* A conflict should be detected. *)
abstract i : index
mutable s : index = i
name n : index->message
system Test = (s := i | if n(s) = n(i) then null).
