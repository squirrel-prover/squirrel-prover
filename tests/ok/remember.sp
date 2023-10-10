system null.

lemma _ (x, y : message) : x = <y,y> => <x,x> = <<y,y>,<y,y>>.
Proof.
 intro H.
 remember <x,x> as z => G.
Abort.

(*------------------------------------------------------------------*)
abstract P : message -> bool.

axiom foo_glob (x : message[glob]) : P x.

global lemma _ x : [P x].
Proof.
  remember x as z => Heq.
  apply foo_glob.
Qed.

global lemma _ t : [P (frame@t)].
Proof. 
  remember (frame@t) as x => Heq. 
  checkfail apply foo_glob exn Failure. (* bad variabe instantiation *)
Abort.
