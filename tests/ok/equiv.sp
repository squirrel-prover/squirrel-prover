set autoIntro=false.

abstract ok : message
abstract ko : message

abstract f : message->message

name n : message
name m : message
name k : message

hash h

channel c

system !_i new a; out(c,a).

equiv test : ok.
equiv test : diff(ok,ko).
equiv test : ok, diff(n,m).
equiv test : f(diff(n,m)).
equiv test : diff(n,h(n,m)).

equiv test : True, if ok = diff(ok,ko) then diff(n,ok).

equiv test (i:index) : output@A(i).

global goal test (i:index) : [happens(A(i))] -> equiv(output@A(i)).

global goal test (i:index) :
  [happens(A(i))] -> equiv(output@A(i)) -> equiv(output@A(i)).
