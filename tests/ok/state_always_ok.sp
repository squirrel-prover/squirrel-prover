

abstract ok : message.
mutable s : message = ok.
channel c
system !_i in(c,x);s:=s;out(c,x).

goal _ (t:timestamp): happens(t) => s@t = ok.
Proof.
  generalize t as t.
  induction => t Hind Hap.
  case t => H. 
  (* t = init *) 
  by expand s.

  (* t = A(i) *) 
  destruct H as [i _].
  expand s.
  by use Hind with pred(A(i)).
Qed.
