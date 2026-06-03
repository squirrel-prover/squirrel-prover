channel c.
abstract u: message.
abstract v: message.
system C = out(c,diff(u,v)).

global axiom L @system:(C/left,C/right) tau : [happens(tau)] ->
equiv(diff(output@tau,v)).


global lemma L' @system:(C/right,C/left) tau : [happens(tau)] ->
equiv(diff(v,output@tau)).
Proof.
intro H .
have A := L tau _ ; 1:auto.
assumption A.
Qed.
