set autoIntro=false.

abstract error : message

channel c.

process reader =
  out(c,error);
  in(c,m);
  if false
  then out(c, error)
  else out(c,error).

system (!_r R: reader).

equiv _ (r:index) : 
[happens(R(r)) =>
(forall (r0:index), (R(r0) < R(r) => r0 <> r)) &&
 forall (i,r0,t:index), (R2(r0) < R(r) => r0 <> r)].
Proof.
 byequiv.
 intro H.
nosimpl((repeat split => r0 _); 
(try (depends R(r0), R1(r0) by auto));
(try (depends R(r0), R2(r0) by auto)); 
auto). 
