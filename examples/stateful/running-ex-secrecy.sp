(**
# RUNNING EXAMPLE - secrecy

In this file we illustrate the articulation between equivalence and
reachability by showing a proof of (weak) secrecy using a strong secrecy
property as hypothesis.
*)

(**
We first declare:

* an indexed name `s0(i)` used to initialize the mutable state `s`;
* a name `m` used to represent a fresh random message.
*)
name s0 : index->message.
mutable s (i:index) : message = s0(i).
name m : message.

(**
In this file, our goal is to prove a secrecy property regardless of any specific
protocol. This is why we declare an empty system.
*)
system null.

(**
The following secrecy property is expressed by a global meta-logic formula.
It states that, if the values stored in the memory cell `s` are strongly
secret (this is expressed by the formula `equiv(frame@tau, diff(s(i)@tau',m))`),
then the value `s(i)@tau'` is weakly secret, _i.e._ the attacker cannot deduce
this value (this is expressed by the formula `[input@tau <> s(i)@tau']`).

Note that `happens(pred(tau))` is needed for the proof, and actually implies
`happens(tau)`.

Note that this global meta-logic formula is defined w.r.t. the same system
(`default/left`) for the left and the right projections.
This is a technical restriction coming from the fact that, in the current
implementation of Squirrel, global and local hypotheses cannot coexist.
*)
global lemma [default/left,default/left] secrecy (i:index,tau,tau':timestamp):
  [happens(pred(tau))]
    -> equiv(frame@tau, diff(s(i)@tau',m))
    -> [input@tau <> s(i)@tau'].
(**
The high-level idea of this proof is to use the strong secrecy hypothesis
to prove the weak secrecy, relying on the `rewrite equiv` tactic which allows
to derive a reachability judgement from an equivalence judgement.
*)
Proof.
  (** We start by introducing the hypotheses. *)
  intro Hap H.
  (** Here, we use the `rewrite equiv` tactic to rewrite the conclusion of the
  goal: all occurrences of left elements from `H` are replaced by their
  corresponding right elements.
  
  In this case, the tactic allows to replace `s(i)@tau'` by the name `m`. *)
  rewrite equiv H.
  (** It remains now to show that the attacker cannot deduce a fresh name,
  using the `fresh` tactic. *)
  intro H'. 
  clear H; const tau. 
  by fresh H'.
Qed.
