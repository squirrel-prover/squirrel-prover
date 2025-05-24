(* check that matching handles global macros that are applied at
   different timestamps. *)

abstract encr : message -> message -> message.
abstract comm : message -> message.
abstract accepte : message -> bool.

channel c.

process A(v:message)
=
in(c,x);
let cm = comm v in
let acc = accepte cm in
out(c,empty).

system P = 
  in(c,v0);
  let v = v0 in
  let cm = comm v in
  Start : out(c,empty);
  A : A(v).

global lemma [P]  _ :
  [happens(A)] -> [happens(Start)] ->
  [v@A = empty]
  ->
  [v@Start = empty].
Proof.
intro H H0 H1.
apply H1.
Qed.

global lemma [P]  _ : 
  [happens(A)] -> [happens(Start)] -> 
  [acc@A]
  -> 
  [accepte (cm@Start)].
Proof.
  intro H H0 H1. 
  apply H1.
Qed.
