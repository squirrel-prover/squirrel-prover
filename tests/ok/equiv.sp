abstract ok : message
abstract ko : message

abstract f : message -> message

name n : message
name m : message
name k : message

hash h

channel c

system !_i new a; out(c,a).

global axiom _ : equiv(ok).
global axiom _ : equiv(diff(ok,ko)).
global axiom _ : equiv(ok, diff(n,m)).
global axiom _ : equiv(f(diff(n,m))).
global axiom _ : equiv(diff(n,h(n,m))).

global axiom _ : equiv(True, if ok = diff(ok,ko) then diff(n,ok)).

global axiom _ (i:index) : equiv(output@A(i)).

global axiom _ (i:index) : [happens(A(i))] -> equiv(output@A(i)).

global axiom _ (i:index) :
  [happens(A(i))] -> equiv(output@A(i)) -> equiv(output@A(i)).
