include Core.
include NonDeduction.

channel c.

system P = !_i A: out(c,empty).

global lemma _ 
  @system:P (u : _[adv])
:
  $( (empty) |> (A u)).
Proof.
  deduce ~all.
Qed.

global lemma _ 
  @system:P (u : _)
:
  $( (u) |> (A u)).
Proof.
  deduce ~all.
Qed.
