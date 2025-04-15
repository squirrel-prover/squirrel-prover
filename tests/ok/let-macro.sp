include Core.

channel c.

op format ['a] : 'a -> message.
op a : message.
op b : message.

(*------------------------------------------------------------------*)
name k : message.

let m : message = k.

lemma [any] _ : m = k.
Proof.
  rewrite /m.
  apply eq_refl.
Qed.

let m' x : message = <k,x>.

lemma [any] _ : m' empty = <k,empty>.
Proof.
  rewrite /m'.
  apply eq_refl.
Qed.

(*------------------------------------------------------------------*)
system Q = !_i in(c,x); A: out(c,empty).
op prop : bool.

(*------------------------------------------------------------------*)
let f0 @system:Q (x : int) u with
| A i     when happens (A i)     -> 0
| init                           -> 1
| _       when not (happens u)   -> 2.
Proof.
auto.
Qed.

(*------------------------------------------------------------------*)
system P = !_i in(c,x); A: out(c,x); !_j B:out(c,x) | D: out(c,empty).

(*------------------------------------------------------------------*)
let f @system:P (x : int) u with
| A i     when happens (A i)     -> <a, format (x,i,u)>
| B (i,j) when happens (B (i,j)) -> <b, format (x,i,j,u)>
| D       when happens D         -> format diff(0,1)
| init                           -> format 0
| _       when not (happens u)   -> format 13.

Proof. 
auto. 
Qed.

lemma [P] _ x i j :
  happens (A i, B (i,j), D) =>
  f x (A i)     = <a, format (x,i,A i)> &&
  f x (B (i,j)) = <b, format (x,i,j,B (i,j))> &&
  f x D         = format diff(0,1). 
Proof.
  intro H.
  rewrite /f. 
  auto.
Qed.

(*------------------------------------------------------------------*)
lemma [P/left] _ x i j :
  happens (A i, B (i,j), D) =>
  f x (A i)     = <a, format (x,i,A i)> &&
  f x (B (i,j)) = <b, format (x,i,j,B (i,j))> &&
  f x D         = format 0. 
Proof.
  intro H.
  rewrite /f. 
  auto.
Qed.

lemma [P/right] _ x i j :
  happens (A i, B (i,j), D) =>
  f x (A i)     = <a, format (x,i,A i)> &&
  f x (B (i,j)) = <b, format (x,i,j,B (i,j))> &&
  f x D         = format 1. 
Proof.
  intro H.
  rewrite /f. 
  auto.
Qed.

lemma [P/left, P/left] _ x i j :
  happens (A i, B (i,j), D) =>
  f x (A i)     = <a, format (x,i,A i)> &&
  f x (B (i,j)) = <b, format (x,i,j,B (i,j))> &&
  f x D         = format 0. 
Proof.
  intro H.
  rewrite /f. 
  auto.
Qed.

(*------------------------------------------------------------------*)
(* `f` is only defined in `P/left` and `P/right` *)
lemma [any/P] _ x i j :
  happens (A i, B (i,j), D) =>
  f x (A i) = <a, format (x,i,A i)> &&
  f x (B (i,j)) = <b, format (x,i,j,B (i,j))>.
Proof.
  intro H.
  checkfail rewrite /f exn Failure.
Abort.


(*------------------------------------------------------------------*)
let g @like:P (x : int) t with
| A i     when happens t -> format (i,0)
| B (i,j) when happens t -> format (i,j,1)
| D       when happens t -> format 2
| init                   -> format 42
| _      when not (happens t) -> format 0.
Proof.
auto.
Qed.

lemma [any/P] _ x i j :
  happens (A i, B (i,j), D) =>
  g x (A i)     = format (i,0) &&
  g x (B (i,j)) = format (i,j,1) &&
  g x D         = format 2.
Proof.
  intro Hap.
  rewrite /g.
  auto.
Qed.
