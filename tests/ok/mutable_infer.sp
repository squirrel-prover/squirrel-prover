(*------------------------------------------------------------------*)
(* check that mutable types are inferred *)
mutable s2 = empty.

abstract i0 : index.

mutable s3 x y z = (x = y && x = i0 && z = i0).
