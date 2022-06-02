(*  *)

(* A simple model using a declared primitive *)
hash h
channel c
process IO = in(c,x);out(c,h(x,try find i such that True in x))
system IO.
