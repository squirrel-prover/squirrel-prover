(*  *)

channel c
channel d
name n:message

system ((in(c,k);out(c,n);null) | (in(c,t);out(d,t);null)).
