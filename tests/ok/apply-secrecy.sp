include Core.

include WeakSecrecy.

(*------------------------------------------------------------------*)
(* `apply` can infers arguments by unification *)
global lemma _ in [any] ['a 'b 'c] (u0 : 'a) (v0 : 'b) (w0 : 'c) :
  $(u0 |> v0) -> $((u0, v0) |> w0) -> $(u0 |> w0).
Proof.
  intro H G. 
  apply Deduction.d_trans _ _ _ H.
  assumption G.
Qed.

global lemma _ in [any] ['a 'b 'c] 
  (u0,u : 'a) (v,v0 : 'b) (w : 'c) (f :  _ -> message[adv]) 
:
  $(u0 |> v0) -> $( (u,u0) |> (f v0) ).
Proof.
  intro H. 
  apply H.
Qed.

global lemma _ in [any] ['a 'b 'c] 
  (u0,u : 'a) (v,v0 : 'b) (w : 'c) (f : _ -> _ -> _ -> message[adv]) 
:
  $(u0 |> v0) -> $( (u,u0) |> (u, v0, f u u0 v0)).
Proof.
  intro H. 
  apply H.
Qed.
