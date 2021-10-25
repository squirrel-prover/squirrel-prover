(*******************************************************************************
RUNNING EXAMPLE - secrecy

In this file we illustrate the articulation between equivalence and 
reachability by showing a proof of (weak) secrecy using a strong secrecy 
property as hypothesis.
*******************************************************************************)

set autoIntro  = false.

name s0 : index->message.
mutable s (i:index) : message = s0(i).
name m : message.

system null.

global goal [default/left,default/left] secrecy (i:index,tau,tau':timestamp):
  [happens(pred(tau))]
    -> equiv(frame@tau, diff(s(i)@tau',m))
    -> [input@tau <> s(i)@tau'].
Proof.
  intro Hap  H.
  rewrite equiv H.
  intro H'.
  by fresh H'.
Qed.
