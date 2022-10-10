channel c

abstract next : message -> message

name n : index -> message

mutable S (i : index) : message = n(i).

system A : !_i S(i) := next(S(i)); out(c,zero).

goal _ (t : timestamp) (i,j:index) :
  happens(t) => S(i)@t = n(j) => i = j.
Proof.
  intro Hap H.
  by fresh H. 
Qed.
