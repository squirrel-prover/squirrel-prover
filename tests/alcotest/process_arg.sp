(*  *)

channel c
(* test process definition *)
process A(m:message) = out(c,m)

system in(c,m);A(m).
