include Core.
include WeakSecrecy.

name n: index -> message.
channel c.

process dummy (i:index)=
out(c,n i).

process ending =
out(c,zero).

system !_i dummy(i) | ending.

lemma  _ (t:_[const]):
  happens(ending,t) =>
  output@ending = zero.
Proof. 
 intro ?. 
 reduce ~macro. 
 true.
Qed.
