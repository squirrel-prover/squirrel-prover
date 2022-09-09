hash h
name k : message
abstract ok : message
channel c

system !_i in(c,x); if fst(x)=h(snd(x),k) then out(c,h(ok,k)).
