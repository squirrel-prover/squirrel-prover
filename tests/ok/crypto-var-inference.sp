include Core.

channel c.

game G = { }.

(*------------------------------------------------------------------*)
system Q = in(c,x); A: out(c, if exists i:index, x = empty then zero).

global lemma _ @system:Q (t:_[adv]) : 
  [happens t] -> 
  equiv(frame@t).
Proof.
  intro H.

  crypto G.
  (* To simulate `frame@t`, we must, among others, simulate 
       `output@A = if exists i, input@A = empty then zero`
     where, by induction, we have `{ input@A | ∀ i : true }`.
     
     `crypto` succeeds because:
       `input@A ∈ { input@A | ∀ i : true }`
     by taking `i = witness` (this is a heuristic: when the value of a
     ∀-variable can't be inferred by matching, it is set to `witness`
     by default).     
   *)
Qed.

(*------------------------------------------------------------------*)
op p : index -> bool.

(* same system but we add that `p i` must hold before `x` *)
system P = in(c,x); out(c, if exists i:index, p i => x = empty then zero).

global lemma _ @system:P (t:_[adv]) : [happens t] -> equiv(frame@t).
Proof.
  intro H.
  crypto G.
  (* Here, to simulate `frame@t`, we must simulate 
       `output@A = if exists i, p i => input@A = empty then zero`
     where, by induction, we have `{ input@A | ∀ j : p j }`.
     
     To succeed, `crypto` must observe that:
       `{input@A | p i } ∈ { input@A | ∀ j : p j }`
     by taking `i = j`. Here, it is done by trying to unify conditions
     during the set member test. *)
Qed.
