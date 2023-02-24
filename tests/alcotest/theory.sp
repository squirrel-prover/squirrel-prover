(* A simple model using a declared primitive *)
hash h
channel c
process IO = in(c,x);out(c,h(x,try find (i : index) such that True in x))
system IO.
