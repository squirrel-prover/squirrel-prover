(*------------------------------------------------------------------*)
include Core.
include NonDeduction.

(* The `NonDeduction` library defines a new predicate `$( u *> v )`. 
   This intuitively means that any attacker function given
   `u` can produce `v` with at most a negligible probability.

   In combination with the deduction predicate `$( u |> v )`, (already
   defined through `Core` which means that there exists an attacker that
   given `u` can produce `v` with overwhelming probability.  

  This tutorial introduces its basic usage, some of its dedicated
  tactics (`deduce`, `fresh`, `prf`), as well as its possible
  interfacing with `crypto` or other tactics like `cdh`.

*)


(* This lemma simply shows that the predicate implies its definition.
  While the actual definition of those predicate can be found in the
  Squirrel library files, this is used to show how to extend a
  predicate to its definition.  *)

global lemma [any] _ ['a 'b] (u:'a) (v:'b) :
  $( u *> v) 
     -> 
       (* For any function from the type of u to the type of v and
       which is [adv], that is ptime with access to the attacker
       randomness, we know that the result of `f u` will not be equal
       to `v` with overwhelming probability. *)
       Forall (f :'a -> 'b [adv]), [ f u <> v].
Proof.
   (* Any global predicate P can be rewritten by using `rewrite /(P)`. *)

   rewrite /( *>). 
   (* not that a space is required here, as ( * without the space
      is the syntax for comments. *)
   intro H. 
   assumption.
Qed.

(* We can similarly expand the definition of the |> predicate. *)
global lemma [any] _ ['a 'b] (u:'a) (v:'b) :
  $( u |> v) 
     -> 
       (* There exists a function from the type of u to the type of v and
       which is [adv], that is ptime with access to the attacker
       randomness, and such that it produces `v` given `u`. *) 
       Exists (f :'a -> 'b [adv]), [ f u = v].
Proof.
   rewrite /(|>). 
   intro H. 
   assumption.
Qed.


(***********************)
(* Basic manipulations *)
(***********************)

(* Proving deduction is partially automated through the `deduce`
tactic, which tries to automatically prove parts of the deduction. *)

name some_secret : message.

global lemma [any] _ u v:
  $( (u, v) |> (fst u, v, if u=v then u, if false then some_secret else u)).
Proof.
  (* The pars of the goals that can be automatically eliminitated are removed. *)
  deduce. 

  (* Here, we still have to prove that `if false then some_secret else
     u` is deducible.  It is of course the case, as it is equal to `u`
     , by deduce failed do see it as it requires equational reasoning,
     and without it, the term depends on some unknown name
     `some_secret`. *)

  (* To conclude, we could prove `[if false then some_secret else u =
  u]`, rewrite the goal with it and then use `deduce` again. *)

   (* Another way to conclude, which would be useful for more complex
cases, is to expand the predicate and explicitely give the witness
deduction function. *)

  rewrite /(|>).
  exists (fun (x: _ * _) => (x#1) ).
   (* We claim that the function returning the first projection of its
   input (and thus `u`) is a valid deduction witness for our case.
   Beware, such an exists is accepted only if Squirrel manages to
   prove that the given function is [adv], which typically requires
   that there are no names inside the function, nor macros. *)

  (* We then have to prove the validity of our witness, which is trivial here. *)
  by simpl.
Qed.

(* Exercice: show that being deducible implies not being secret. *)
global lemma [any] _ ['a 'b] (u:'a) (v:'b) :
  $( u |> v) ->  $( u *> v) -> [false].
Proof.
  (* Solution *)
  intro Ded. 
  intro nDed.

  rewrite /(|>) in Ded.
  destruct Ded as [f Eq].

  rewrite /( *>) in nDed.
  have Neq := nDed f.
  auto.
Qed.

(* As a bonus exercice, justify, on paper, why the converse of the
previous statement does not hold. *)

(* Deduction is transitive, and this can be used automatically through the `deduce with` instruction. *)
global lemma [any] _ (u : int) (v : int) (w : int) : 
    $(u |> v) ->
    $(v |> w) ->
    $(u |> w).
Proof.
intro A B.

(* As B enables to deduce `w`, we can use it to simplify our goal *)
deduce with B.

(* We now explicitely have A as conclusion. *)
assumption.
Qed.

(* Exercise: proof the previous statement without using deduce. *)
global lemma [any] _ ['a 'b 'c]  (u : 'a) (v : 'b) (w : 'c) : 
    $(u |> v) ->
    $(v |> w) ->
    $(u |> w).
Proof.
  (* Solution *)
intro A B.

rewrite /(|>) in *.
destruct A as [fA EqA].
destruct B as [fB EqB].

exists (fun x => fB (fA x)).
by simpl.
Qed.


(*------------------------------------------------------------------*)
(* Deduction and secrecy can be powerfully mixed together to
e.g. simplify the left hand-side of a secrecy goal by something that
deduces it, but preserves secrecy.*)
(* Exercise: prove it *)
global lemma [any] _ ['a 'b 'c]  (u : 'a) (v : 'b) (w : 'c) : 
    $(u *> w) ->
    $(u |> v) ->
    $(v *> w).
Proof.
  (* Solution *)
   intro @/( |> ) @/( *> ) H1 [f H2] g.
   have A /= := H1 (fun x => g(f x)).
   auto.
Qed.


(***********************)
(*  Dedicated Tactics  *)
(***********************)

(* Some tactics are dedicated to proving secrecy. *)


(* `fresh` is similar to its original tactic, and enables proving that
a name with is fresh on the left hand side cannot be deduced. *)

system null.

global lemma _ : 
 $( (zero) *> some_secret ).
Proof.
  by fresh.
Qed.

(* note that the fresh tactic is only adapted for quality of life. One could already prove the previous statement by expanding the predicate and using fresh on the equality. *)

(* Exercise four: do the previous, using fresh on an equality. *)
global lemma _ : 
 $( (zero) *> some_secret ).
Proof.
  rewrite /( *>). 
  (* solution *)
  intro f.
  intro Eq.
  fresh Eq.
Qed.


(* `prf` is a dedicated tactic, not only quality of life, which is very expressive for secrecy and has many options. We describe here its two main usages.  *)
name key : message.
hash h.



(* A PRF hash function, produces a fresh random name, so on the right
hand side, `prf ~right` can be used to prove that a hash is secret. *)

global lemma _ (u,v:message [const]):
  $(  u *> (h(v,key))) .
Proof.

  prf ~right 0.
  (* prf targets an element of a tuple. Here, on the right hand side, we have a single element, hence the 0. *)

Qed.

(* When the attacker can compute hash values through a ROM oracle,
`prf ~right` then requires to prove the secrecy of the input of the
hash. In addition, the hash value must never have been hashed before
similarly to the equivalence `prf` tactic.  *)


global lemma _ (u:message [const]):
  $( (fun x : message => h(x,key), h(u,key)) *> (h(some_secret,key))) .
Proof.

  prf ~right 0.

  (* First, we must prove that `some_secret` was not hashed before, so
  we must show that it was not hashed in `h*u,key)`.  *)
  +  intro Eq. 
     by fresh Eq.

  (* Second, we must prove that the attacker cannot compute
  `some_secret`, otherwise it could use the ROM `fun x : message =>
  h(x,key)` to compute the target value. *)
 + by fresh.  
Qed.


(* Exercise: show that the hash of a hash of a name is secret*)
global lemma _ (u:message [const]):  
  $( (fun x : message => h(x,key), h(u,key)) *> (h(h(some_secret,key),key))) .
Proof.
  (* Solution *)
  prf ~right 0.
  + intro Eq. 
    by euf Eq.
   
  + prf ~right 0.
   ++ intro Eq.
      by fresh Eq.
   ++ by fresh.
Qed.



(* When proving secrecy with a hash computation on the left-hand side,
one can notice that if this hash is a fresh one, it is in fact a fresh
random value, that does not help the attacker to conclude. Hencer `prf
~left` enables one to remove a fresh hash on the left. *)

global lemma _ (u:message[const]) :
   $( (u,h(some_secret,key)) *> some_secret ). 
Proof.

  (* `prf` can remove the hash on the left hand_side, without any
  additional subgoal as there is no other hash nor ROM. *)

  prf ~left 1. (* here, the element number 1 of the lhs tuple is our target hash. *)

  (* without the hash, we now have a fresh value. *)

  by fresh.  
Qed.



(* Exercise: show that the hash of a name is secret, even if the hash of the hash of this name is known. *)
global lemma _ (u:message [const]):  
  $( (fun x : message => h(x,key), h(h(some_secret,key),key)) *> (h(some_secret,key))) .
Proof.
  (* Solution *)
  prf ~left 1.
  + intro Eq. 
    by euf Eq.
   
  + prf ~right 0.
    by fresh.
Qed.

(**************************)
(* Mini protocol examples *)
(**************************)

(* 
   `cdh/gdh` can also be used to prove secrecy goals. 
    Let us define a DH type and a system that reveals some DH public keys.  

 *)
type E[large, finite].

gdh g, (^), ( ** ) where group:message exponents:E.

name a : index -> E.
name b : index -> E.

channel c.

process A (i : index) = A: out(c, <g^ (a i), g^(b i)>).

system CDH = !_i A(i).


(* Recall that when we have an equation `E: w = g^(u*v)`, `cdh E,g`
can be called to close the goal, if `u` and `v` are correctly used in `w`. *)

(* Exercise: prove that all shared keys are secrets. *)
global lemma [CDH] _ (i : index[adv]) : 
  [happens(A i)] -> 
  $( (output@A(i)) *> (g^ (a i ** b i))).
Proof.
  (* Solution *)
  intro Hap. 
  rewrite /( *> ) => f.
 
  intro H. 
  cdh H, g.
Qed.


(* Any tactic talking about equalities can similarly be used as in the previous way.  *)

(* Further, one can also write `crypto` games aimed at reasoning over equivalences and then apply them. *)
(* ------------------------------------------------------------------- *)
game CDH = {
   rnd A : E;
   rnd B : E;

   oracle ga = { return g ^ A; }
   oracle gb = { return g ^ B; }

   oracle challenge  m = { return diff(m <> g ^ (A ** B), true); }
   oracle challenge' m = { return diff(m <> g ^ (B ** A), true); }
}.

(* The previous goal can then be proved using `crypto`, which however requires some manipulations. *)
global lemma [CDH] _ (i : index[adv]) :
  [happens(A i)] ->
  $( (output@A(i)) *> (g^ (a i ** b i))).
Proof.
  intro Hap.
  rewrite /( *> ) => f.

  ghave HLeft :
    equiv( diff(f (output@A(i)) <> g^ (a i ** b i), true) ).
  by crypto CDH.
  ghave HRight :
    equiv( diff(true, f (output@A(i)) <> g^ (a i ** b i)) ) by sym; crypto CDH.
  project.
  + by rewrite equiv HLeft.
  + by rewrite equiv -HRight.
Qed.



(* With a protocol with an explicit ROM in its actions, (weak) secrecy, modelled with
non-deduction, can be easily lifted to real-or-random secrecy, as follows. *)

process ROM (i : index) = R: in(c,x); out(c, h(x,key)).



system CDH_ROM = !_i A(i) | !_j ROM(j).

(* Let us assume we proved the weak secrecy of the keys `g^(a i*b i)`
 even with the additional ROM, and with the full frame on the left
 hand side. (proved similarly to before but with an induction) *)


global axiom [set:CDH_ROM/left; equiv:CDH_ROM] weak_secrecy (t:timestamp [const]) (i : index[const]) : 
  [happens(t)] -> 
  $( (frame@t) *> (g^ (a i ** b i))).


(* Exerice: use this weak secrecy proof to prove the secrecy of a key
derived using the ROM and a `g^(a i*b i)`. *)

name fresh_key : message.

global lemma [CDH_ROM] strong_secrecy (t:timestamp [const]) (i : index[const]) : 
  [happens(t)] ->   
  equiv(frame@t) -> (* for simplicity, we assume we proved the equivalence for the frame alone. *) 
  equiv(frame@t, diff( h(g^ (a i ** b i), key), fresh_key)).
Proof.
intro Hap Equiv.

prf 1. 
  
 { (* Here, PRF finds a collision with a potential ROM action, and we
 must prove that the target hash was never computed in the ROM. We can
 do so using the axiom. *)

   (* Solution *)
   intro j Ord Eq. 
   rewrite /input in Eq. 
   have Ax := weak_secrecy (pred (R j)) i _. constraints.
   rewrite /( *>) in Ax.
   by have _ := Ax att.
}
   
   fresh 1. assumption.

assumption.
Qed.
