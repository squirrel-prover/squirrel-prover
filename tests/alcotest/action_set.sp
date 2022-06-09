(*  *)

channel c
mutable s(i:index): message = empty
system !_i in(c,x); s(i):=x.
