set autoIntro=false.

abstract ok : message
mutable s : message
channel c
system !_i in(c,x);s:=s;out(c,x).

axiom init_ok : s@init = ok.

goal _ (t:timestamp): happens(t) => s@t = ok.
Proof.
  induction.
  intro Hind Hap.
  case t. 
  (* t = init *)
  by use init_ok. 

  (* t = A(i) *) 
  destruct H as [i _].
  by use Hind with pred(A(i)).
Qed.
