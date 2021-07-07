(* set autoIntro=false. *)

name n : message
channel c
(* We should not be able to write things like this! *)
system out(c,output@init).
