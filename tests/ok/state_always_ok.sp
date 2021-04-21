set autoIntro=false.

abstract ok : message.
mutable s : message = ok.
channel c
system !_i in(c,x);s:=s;out(c,x).

set debugCompletion=true.
set debugTactics=true.
goal _ (t:timestamp): happens(t) => s@t = ok.
Proof.
  induction.
  intro Hind Hap.
  case t. 
  (* t = init *) 
  by expand s.

  (* t = A(i) *) 
  destruct H as [i _].
  expand s.
  by use Hind with pred(A(i)).
Qed.
