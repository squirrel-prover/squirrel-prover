(*  *)

channel c
name n:message
system let x = n in out(c,x); !_i in(c,y); let z = x in out(c,<x,z>).
