channel c.

mutable s(i:index,j:index): message = empty
name ok:message
system !_j in(c,x); try find i such that x = s i j in out(c,ok).
