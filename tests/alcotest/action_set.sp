(* set autoIntro=false. *)

channel c
mutable s:index->message
system !_i in(c,x); s(i):=x.
