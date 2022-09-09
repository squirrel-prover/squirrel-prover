channel c
name k : index->message
process P(x:message) = out(c,x)
system !_i !_i P(k(i)).
