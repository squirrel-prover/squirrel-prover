

hash h
name k:message
name cst:message

channel ch

name n : index -> message

system O:
 in(ch,x); if x=k then out(ch,x).

goal _ : happens(O1) => cond@O1 => input@O1 <>k.
Proof.
  intro Hap Hc. 
  by expand cond@O1.
Qed.

goal _: happens(O) => exec@O => output@O = k.
Proof.
 intro _ _. 

 expand exec@O.
 expand cond@O. 
 expand output@O.
 auto.
Qed.

goal _:
happens(O) => 
frame@O = <frame@pred(O),<of_bool(exec@O),if exec@O then output@O else zero>>.
Proof. 
  intro *. 
  by expand frame.
Qed.
