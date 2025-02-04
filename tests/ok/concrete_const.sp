include Real.
open Real.

type toto[finite]. 

op e : toto -> Real.t.

system P = null.

axiom [any] foo (x : toto) : x = witness <: e x.

exact axiom [any] bar : sum (fun (x:toto) => true) (fun x => e x) <= of_int 1.

lemma [any] _ (x : toto) : x = witness <: of_int 1.
Proof.
  const x <: (fun (x : _) => e x). 
  + apply bar.                    (* FEAT: eta-expand during unification *)
  + by apply foo. 
Qed.

(*------------------------------------------------------------------*)
type bad.

lemma [any] _ (x : bad) (e : bad -> Real.t) : x = witness <: of_int 1.
Proof. 
  checkfail const x <: (fun (x : _) => e x) exn Failure. 
  (* Failure: type should be finite *)
Abort.

(*------------------------------------------------------------------*)
system null.

global axiom foo_r (i : index[const]) e : [false <: e].

(* test the concrete logic *)
global lemma _ (i : index) e : [i = i <: e] -> [false <: e].
Proof. 
  intro H.
  checkfail have G := (foo_r i e) exn Failure.
  (* `i` is not constant because it appears in `H` *) 

  (* clearing `H` does **not** yields a constant `i`, because we are
  in the concrete logic. *)
  clear H.
  checkfail have G := foo_r i e exn Failure.
Abort.

op a : index.

op eGoal : Real.t.
op eH : Real.t.

exact axiom bar2 b :
  sum (fun (i:index) => true) (fun (i:index) => b i) <= eGoal - eH.

axiom bar3 (b : index -> Real.t) i : false <: b i.

global lemma _ (i : index) (b : index -> Real.t) :  
  [i = a <: eH] -> [false <: eGoal].
Proof. 
 intro H.
  const i <: (fun x => b x).

  + (* subgoal requiring to prove that the provided bound is smaller
       than `eGoal`, to which we must substract `eH`, since `H` is
       localized by `const` *)
    apply bar2.
  + checkfail localize H as H0 exn Failure. (* `H` already local *)
    by apply bar3 b i.    
Qed.
