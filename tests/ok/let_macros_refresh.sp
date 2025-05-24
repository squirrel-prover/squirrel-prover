channel c.
process P = let x1 = empty in let x2 = <x1,x1> in out(c,<x1,x2>).
system (P | P).
