hash h
name k:message
name cst:message

channel ch

name n : index -> message

system O:
 in(ch,x); if x=k then out(ch,x).


goal dummy :
cond@O1 => input@O1 <>k.
Proof.
simpl.
expand cond@O1.
notleft H0.
Qed.

goal
exec@O =>
  output@O = k.
 Proof.
simpl.

expand exec@O.
expand cond@O.
Qed.

goal
 frame@O = <frame@pred(O),<if exec@O then true else false,if exec@O then output@O else zero>>.
Proof.
simpl.
Qed.
