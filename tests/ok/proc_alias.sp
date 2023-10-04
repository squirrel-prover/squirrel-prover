channel c.

process A = out(c,empty)
process B = A
process C = Y: B

system C.

(* check that the action is indeed named `Y` *)
lemma _ : happens(Y) => output@Y = empty. 
Proof. auto. Qed.

system [P] ((Y: B) | (Z: B)).

(* check that the action is indeed named `Y` *)
lemma [P]  _ : happens(Y,Z) => output@Y = empty && output@Z = empty. 
Proof. auto. Qed.
