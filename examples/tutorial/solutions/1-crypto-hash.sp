(*******************************************************************************
# Cryptographic primitives : hash functions

*******************************************************************************)

include Core.

(* ----------------------------------------------------------------- *)
(** We first declare a few constants and names to be used later. *)

abstract a : message.
abstract b : message.
abstract c : message.

name n : message.
name m : message.

name k  : message.
name k' : index -> message.

system null.

(* ----------------------------------------------------------------- *)
(** ## Hash functions *)

hash h.

(** We have declared [h] as a keyed hash function satisfying
    the PRF assumption: it is a family of pseudorandom functions.
    Our functions also satisfy collision resistance, which
    enables the `collision` tactic. *)
lemma _ : h(a,k) = h(b,k) => a = b.
Proof.
  intro H.
  (* The collision tactic applies to an equality
     h(u,k) = h(v,k) where h is a hash function, and adds
     the equalities u = v as hypothesis.
     In this example, the equality deduced is
     introduced right away using =>. *)
  collision H; intro Hcoll.
  auto.
Qed.

lemma hash_1 : h(h(a,k),k) = h(h(b,k),k) => a = b.
Proof.
  (* BEGIN EXO *)
  intro H.
  collision H => H'.
  collision H' => H''. 
  assumption.
  (* END EXO *)
Qed.

(** PRF also implies EUF (unforgeability).
    This is expressed through the `euf` tactic. *)
lemma _ : <h(b,k), h(c,k)> = h(a,k) => a = b || a = c.
Proof.
  intro H.
  (* The euf tactic must be invoked on an assumption
     of the form `h(u,k) = v` (or the converse).
     From this it deduces that `u` must be equal to one
     of the messages that is hashed (using `k`) inside
     `u` or `v`: for each case in this disjunction it introduces
     a new subgoal with corresponding hypotheses.
     In the next example we have two subgoals.
     Look carefully at the Heuf assumption in each one. *)
  euf H; intro Heuf.
  + auto.
  + auto.
Qed.

lemma hash_2 : h(a,k) <> a. (* We could similarly prove `h(a,k) <> b`. *)
Proof.
  (* BEGIN EXO *)
  intro H.
  euf H.
  (* END EXO *)
Qed.

lemma hash_3 : h(a,k) = h(h(a,k),k) => h(a,k) = a.
Proof.
  (* This is easily proved using `collision`.
     Try doing it with EUF only!
     Be careful: a straightforward application of `euf` in this
     case does not bring any extra hypothesis. *)
  (* BEGIN EXO *)
  intro H.
  have H' : h(h(a,k),k) = h(a,k) by auto.
  euf H' => H''.
  auto.
  (* END EXO *)
Qed.

(* The euf tactic also reasons about indices.
   For the equality `h(u,k(i)) = v`, it needs to consider all possibles
   hashes `h(w,k(j))`, under the assumption that `i = j`.
   This allows to prove the next lemma. *)
lemma hash_4 (i,j:index) : h(a, k'(i)) = h(a, k'(j)) => i = j.
Proof.
  (* BEGIN EXO *)
  intro H.
  euf H.
  auto.
  (* END EXO *)
Qed.


global lemma hash_5_lemma : equiv(diff(h(a,k),n),m).
Proof.
  prf 0.
  (* The `prf` tactic replaced the hash `h(a,k)` with a fresh name.
     It first checked that `a` has never been hashed before. *)
  by fresh 0.
Qed.

global lemma hash_6 :
  [a <> b] -> 
  equiv(diff(h(a,k),n),diff(h(b,k),m)). 
Proof.
  (* BEGIN EXO *) 
  intro H.
  prf 0; 1:auto.
  prf 1.
  fresh 0; 1:auto.
  fresh 0; 1:auto.
  refl.
  (* END EXO *) 
Qed.
