include Real. include Int.
open Real. open Int.

op a : bool.
op d : bool.

exact axiom fooA @system:any : a.
exact axiom fooD @system:any : d.

(* apply `concrete` in `concrete` (from a hypothesis), succeed *)
global lemma _ @system:any b c :
  [a => b => c <: of_int 42] ->
  [(d => b) => c <: of_int 24].
Proof.
  intro H. 
  intro G.
  apply localize(H) in G.
  + apply fooD.
  + apply fooA.
  + reduce.
    have A : c <: of_int (-18) by admit.
    assumption A.
Qed.

axiom axL @system:any b c : b => c <: of_int 42.
global axiom axG @system:any b c : [b => c <: of_int 42].

(* apply `concrete` in `concrete` (from a local lemma), succeed *)
global lemma _ @system:any b c e :
  [b => c <: e].
Proof.
  simpl.
  intro G.
  apply (axL _ c) in G.
  weak z. {
    have A : e - of_int 42 = z by admit.
    by rewrite A.
  }
  assumption G.
Qed.

(* apply `concrete` in `concrete` (from a global lemma), succeed *)
global lemma _ @system:any b c e :
  [b => c <: e].
Proof.
  simpl.
  intro G.
  (* FEAT: allow to avoid localizing here 
     (and do the same for simple `apply`)? *)
  apply localize(axG _ c) in G.
  weak z. {
    have A : e - of_int 42 = z by admit.
    by rewrite A.
  }
  assumption G.
Qed.

(* apply `concrete` in `asymptotic`, fail *)
global lemma _ @system:any b c :
  [a => b => c <: of_int 42] ->
  [(d => b) => c].
Proof.
  intro H. 
  intro G.
  checkfail apply localize(H) in G exn Failure.
Abort.

(* apply `asymptotic` in `concrete`, fail *)
global lemma _ @system:any b c :
  [a => b => c] ->
  [(d => b) => c <: of_int 24].
Proof.
  intro H. 
  intro G. 
  checkfail apply localize(H) in G exn Failure.
Abort.

(* apply `local` in `concrete`, fails  *)
global lemma _ @system:any p q (u,v : int) e :
  [q u <: e] ->
  [(forall x, p x => q x) => false <: e].
Proof.
  intro Ax.
  intro H. 
  checkfail apply H in Ax exn Failure.
Abort.
