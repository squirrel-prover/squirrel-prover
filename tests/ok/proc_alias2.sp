channel c.

process A = $U: out(c,empty); $V: out(c,zero).
process B = A.
process C = Y: B.

system C.

(* check that the action is indeed named `YA` *)
lemma _ : happens(YU,YV) => output@YU = empty && output@YV = zero. 
Proof. auto. Qed.

system [P] ((Y: B) | (Z: B)).

(* check that the action is indeed named `Y` *)
lemma [P]  _ : 
  happens(YU,YV,ZU,ZV) => 
  output@YU = empty && output@YV = zero &&
  output@ZU = empty && output@ZV = zero.
Proof. auto. Qed.
