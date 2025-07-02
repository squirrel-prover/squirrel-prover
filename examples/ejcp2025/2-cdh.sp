(*******************************************************************

# Tutorial on using the CDH (Computational Diffie-Hellman) assumption.

 *******************************************************************)

(* The next two lines are setup and should be ignored. *)
include Logic.
system null.

(* --------------------------------------------------------------------- *)
(** ## Declaring a Diffie-Hellman group *)

type exponent.

cdh g, (^), ( ** ) where group:message exponents:exponent.
(* We can specify the type to use for group elements and exponents. *)


(** We can postulate the following expected identities
    as axioms -- which Squirrel could implicitly declare with cdh. *)

axiom ax_exp_mul (a,b:exponent) :  (g ^ a) ^ b = g ^ (a ** b).
axiom ax_mul (a,b:exponent) :  a ** b = b ** a.

(* --------------------------------------------------------------------- *)
(** ## CDH tactic *)

(** The CDH assumption states that, if a and b are randomly sampled
    and both (g ^ a) and (g ^ b) are given to the attacker, then
    the attacker has a negligible probability of guessing g ^ (a ** b).

    The assumption comes implicitly with the cdh declaration and is made
    available through the cdh tactic.
    The assumption implies, in particular, that exponents
    cannot be enumerated in polynomial time. *)

abstract (+) : message -> message -> message.

name a : exponent.
name b : exponent.

(** The following identity would contradict CDH. *)
lemma _ : g ^ (a ** b) = (g ^ a) + (g ^ b) => false.
Proof.
  intro H.
  cdh H, g.
Qed.

(** Generalizing the previous example. *)
lemma _ : g ^ (a ** b) = att (< g ^ a, g ^ b >) => false.
Proof.
  intro H.
  cdh H, g.
Qed.

(** This identity is of course not a consequence of CDH,
    because b is used directly, not as part of (g ^ b). *)
lemma _ : g ^ (a ** b) = (g ^ a) ^ b => false.
Proof.
  intro H.
  cdh H, g.
Abort.

(* --------------------------------------------------------------------- *)
(** ## Indexed exponents *)

(** In order to better understand how the tactic works, it is useful
    to consider similar examples but with indexed exponents,
    i.e. unbounded collections of exponents. *)

name a' : index -> exponent.
name b' : index -> exponent.

lemma _ (i,j,k:index) : g ^ (a' i ** b' i) = (g ^ a' j) ^ b' k => i = k.
Proof.
  intro H.
  cdh H, g.
  auto.
Qed.

lemma _ (i,j:index) : g ^ (a' i ** b' j) = (g ^ a' i) + (g ^ b' j) => false.
Proof.
  intro H.
  cdh H, g.
Qed.

(* --------------------------------------------------------------------- *)
(** ## Exercises *)

(* A simple variant of a previous example.
   The cdh tactic views (g ^ a ^ b) directly as (g ^ a**b)
   so it is not necessary to use ax_exp_mul to help it. *)
lemma _ :
  att (< g ^ a, g ^ b >) = g ^ a ^ b =>
  false.
Proof.
  (* TODO *) admit.
Qed.

(* A not-so-simple variant of a previous example.
   Here the tactic does not immediately work but you can reformulate
   the goal to help it. Beware that, when called on an hypothesis of the
   form (g ^ a ** b) = (g ^ c ** d) it will work with c and d as exponents
   in priority. The same goes with g^a^b and g^c^d. *)
lemma _ (i,j:index) : g ^ (a' i ** b' i) = (g ^ a' j) ^ b' i => j = i.
Proof.
  (* TODO *) admit.
Qed.
