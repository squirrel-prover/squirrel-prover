

channel c.

abstract a : index -> message
abstract b : index -> message

mutable S (i : index) : message = a(i).

process B(i,j : index) =
  in(c,x);
  S(i) := b(j);
  out(c,zero).  

system !_i !_j B(i, j).

include Basic.

(*------------------------------------------------------------------*)
(* macro expantion under binders *)

goal _ (t : timestamp, u : index) : 
 happens(t) => (S(u)@t = a(u) || exists (k : index) S(u)@t = b(k)).
Proof.
 induction t => t Hind Hap.
 case t => Heq.

 by left.

 repeat destruct Heq as [_ Heq]. 
 reduce.
 case u = i => /= _. 
 by right; exists j.
 by apply Hind.
Qed.
