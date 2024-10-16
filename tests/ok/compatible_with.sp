op a : message.
op b : message.

channel c.

system P = A: out(c,a).
system Q = A: out(c,b).

global axiom [set:P; equiv:Q] bar : equiv(output@A).

axiom [any/P] foo : A = A.
