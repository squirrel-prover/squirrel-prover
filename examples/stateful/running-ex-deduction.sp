(*******************************************************************************
RUNNING EXAMPLE

This protocol is a variant of the OSK protocol described in:
M. Ohkubo, K. Suzuki, S. Kinoshita et al.,
“Cryptographic approach to “privacy-friendly” tags,”
RFID privacy workshop, vol. 82. Cambridge, USA, 2003.

Each tag is associated to a mutable state sT initialized with s0.
Readers have access to a database containing an entry sR for each authorized
tag.

         sT := H(sT,k)
T -> R : G(sT,k')

         input x; sR := H(sR,k) if x = G(H(sR,k),k') with sR in DB
R -> T : ok

COMMENTS
- In this model we only consider tags (no hash oracles, no readers)
  the goal is to illustrate a realistic use of `apply ~inductive`
  on a minimal example.

*******************************************************************************)
hash H
hash G
name k : message
name k' : message

name s0  : index -> message
name s0b : index -> message     (* renamed identities *)

mutable sT(i:index) : message = empty

abstract ok : message
channel cT

process tag(i:index) =
  sT(i):=H(sT(i),k);
  out(cT,G(sT(i),k'))

system !_i sT(i):=diff(s0(i),s0b(i)); !_j T: tag(i).

include Basic.

set showStrengthenedHyp=true.

(* AXIOMS *)

(* Uniqueness of states:
   it is easily proved in other similar examples, we leave it out here. *)
axiom h_unique (i,i',j,j':index):
  sT(i)@T(i,j) = sT(i')@T(i',j') => (i = i' && j = j').

(* Indistinguishability between the sequences of initial states,
   before and after renaming. This is essentially an instance of the
   "fresh" tactic, but to do it within the tool we miss an induction
   principle over sequences. *)
global axiom fresh_names :
  equiv(seq(i:index=>diff(s0(i),s0b(i)))).

global lemma fresh_names_k :
  equiv(k, seq(i:index=>diff(s0(i),s0b(i)))).
Proof.
  fresh 0; 1:auto.
  apply fresh_names.
Qed.

(* PROOFS *)

(* Observational equivalence with seeds and k as extra data:
   the proof would be the same without the extra data (except for the easy base case)
   which does not depend on t. *)
global lemma equiv_with_seed (t : timestamp[const]):
  [happens(t)] ->
  equiv(frame@t, k, seq(i:index=>diff(s0(i),s0b(i)))).
Proof.
  intro Hap.
  induction t.

  (* Init *)
  + fresh 1; 1:auto.
    expand frame; apply fresh_names.

  (* A: initialize sT *)
  + expandall. fa !<_,_>. apply IH.

  + expandall. fa !<_,_>, (if _ then _).
    prf 1. 
      intro i0 j0 H Heq. use
      h_unique with i0, i, j0, j; 2: auto.
      by destruct H0.
    fresh 1; 1:auto.
    by apply IH.
Qed.

(* With apply ~inductive we easily obtain all the past values of sT
   from the seeds and k. *)
global lemma equiv_with_states_inductive (t : timestamp[const]):
  [happens(t)] ->
  equiv(frame@t, k, seq(i:index,t':timestamp => if t'<=t then sT(i)@t')).
Proof.
  intro Hap.
  apply ~inductive equiv_with_seed t; assumption.
Qed.

(* We now illustrate how the proof could go without the use of
   `apply ~inductive`. *)

lemma neq_leq_lemma (t,t':timestamp): ((not(t=t')) && t<=t') = (t<=pred(t')).
Proof.
 rewrite eq_iff.
 by case t.
Qed.

global lemma equiv_with_states_manual (t : timestamp[const]):
  [happens(t)] ->
  equiv(frame@t, k, seq(i:index,t':timestamp => if t'<=t then sT(i)@t')).
Proof.
  intro Hap.
  induction t.

  ++
  (* The base case requires rewriting inside the sequence. *)
  have -> :
     (seq(i:index,t':timestamp => if t'<=init then sT(i)@t')) =
     (seq(i:index,t':timestamp => if t'<=init then empty));
  1: by fa; fa.
  expand frame; apply fresh_names_k.

  ++
  (* Case A *)
  (* TODO Complete this case or make it possible to initialize sT differently
     for each single system.
     This has changed since the acceptance of the CSF'22 paper. *)
  admit.

  ++
  (* Case T *)
  expandall.
  fa !<_,_>, if _ then _.
  (* Get rid of item 1 using PRF, as before. *)
  prf 1.
    intro i0 j0 H Heq. 
    by use h_unique with i0, i, j0, j.
  fresh 1; 1:auto.
  (* We now have to work on our sequence to remove the last element.
     This is done using splitseq to single out some elements,
     and then perform some rewriting inside the sequences. *)
  splitseq 2: (fun (i0:index,t':timestamp) => t'=T(i,j)).
  rewrite /= !if_then_then.

  (* We still can't conclude by IH. The sequence in position 2 is bi-deducible
     but to show it one needs to do a case analysis on i=i0 since the value
     of sT(i0)@T(i,j) depends on it. *)
  checkfail apply IH exn ApplyMatchFailure.
  splitseq 2: (fun (i0:index,t':timestamp) => i0=i).
  rewrite /= !if_then_then.

  (* More rewriting inside sequences. *)
  rewrite /sT.
  (* At this point our automatic bi-deduction checker cannot verify that
     items 2 and 3 are bi-deducible. Its implementation could be improved
     to complete this tedious proof. *)
  try apply ~inductive IH. admit.
Qed.
