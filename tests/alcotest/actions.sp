(*  *)

(* Testing block creation, input terms and index management *)
channel c
process IO = in(c,x);out(c,<x,x>)
process IOIO = in(c,x);out(c,x);in(c,y);out(c,<x,y>)
system (IO | (IOIO1: IOIO) | !_i (IOi: IO) | !_i !_j (IOij: IO)).
