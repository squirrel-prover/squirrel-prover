(*  *)

channel c
system (new n; in(c,x); new m; out(c,<x,n>); new p; out(c,p) |
        !_i in(c,x);new n;out(c,n)).
