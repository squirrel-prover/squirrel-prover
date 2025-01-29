include Core.

system null.
abstract a :message.

game Random ={
  oracle rand  = {
  rnd n : message;
  return diff(n,a)}}.

name n : index -> message.
abstract i:index.


global lemma _ :
equiv(fun j => diff(n(j),a), diff(n(i),a)).
Proof.
crypto Random.
auto.
Qed.


global lemma _ : 
equiv(diff(n(i),a),fun (j:index) => diff(n(i),a)).
Proof.
crypto Random.
Qed.

(* We need the unicity of a minimal element of index
to make the proof works.
axiom *)

axiom min_index : 
forall (m,m':index), 
(forall j:index, not (j < m)) 
=> (forall j:index, not (j < m'))
=> (m = m').


global lemma _ : 
equiv((fun (j:index) => diff(n(i),a))).
Proof.
crypto Random.
intro k k0.
intro [H H0].
intro Neq.
have min := min_index k0 k H0 H.
auto.
Qed.

(*------------------------------------------------------------------*)
global lemma _ : 
equiv((fun (j:message) => diff(n(i),a))).
Proof.
checkfail crypto Random exn Failure.
Abort.

(*------------------------------------------------------------------*)
global lemma _ : 
equiv(
  fun (j:index) => diff(n(i),a), 
  diff(n(i),a)
).
Proof.
crypto Random.
intro k k0.
intro [H H0].
intro Neq.
by have min := min_index k0 k H0 H.
Qed.

(*------------------------------------------------------------------*)
global lemma _ : 
equiv(
  fun (j:index) => (diff(n(i),a), diff(n(i),a)),
  diff(n(i),a)
).
Proof.
crypto Random.
intro k k0.
intro [H H0].
intro Neq.
by have min := min_index k0 k H0 H.
Qed.

(*------------------------------------------------------------------*)
op p : index -> bool.
op jc : index.

axiom total (k,k':index) : k < k' || k > k' || k = k'. 

(* Check that we cannot compute the last `diff(n i,a)` using the 
   game, since we do not know whether we already computed it 
   during the recursive computation for the `fun`. *)
global lemma _ : 
equiv(
  fun (j:index) => if p j then diff(n(i),a),
  diff(n(i),a)
).
Proof.
crypto Random.
+ intro k k0 [Hl H Hl0 H0] Neq.
  have [A  | ?] // := Hl  k0 => {Hl}.
  have [A0 | ?] // := Hl0 k  => {Hl0}.
  have [] := total k k0.
  - smt.
  - rewrite /( > ). 
    smt.
  - smt.
+ intro k [H H1].
  (* check that we get the proof-goal resulting from the local
     randomness reuse between an oracle call in the `fun` and the
     oracle call for the last `diff(n i, a)` (which we cannot prove):

        H: forall (j:index), not (j < k) || not (p j)
        H1: p k
        ----------------------------------------
        i <> i 
 *)
  have A : forall (j:index), not (j < k) || not (p j) by assumption H => {A H}.
  have A : p k by assumption H1 => {A}.
  have A : i <> i by admit. 
  assumption A. 
Qed.

(*------------------------------------------------------------------*)
global lemma _ : 
equiv(
  fun (j:index) => if p j then diff(n(i),a),
  if p jc then diff(n(i),a)
).
Proof.
crypto Random.
+ intro k k0 [Hl H Hl0 H0] Neq.
  have [A  | ?] // := Hl  k0 => {Hl}.
  have [A0 | ?] // := Hl0 k  => {Hl0}.
  have [] := total k k0.
  - smt.
  - rewrite /( > ). 
    smt.
  - smt.
Qed.

(*------------------------------------------------------------------*)
op q j = p j. 

(* same as above, but using `q jc` rather than `p jc`  *)
global lemma _ : 
equiv(
  fun (j:index) => if p j then diff(n(i),a),
  if q jc then diff(n(i),a)
).
Proof.
crypto Random.
+ intro k k0 [Hl H Hl0 H0] Neq.
  have [A  | ?] // := Hl  k0 => {Hl}.
  have [A0 | ?] // := Hl0 k  => {Hl0}.
  have [] := total k k0.
  - smt.
  - rewrite /( > ). 
    smt.
  - smt.
Qed.

(*------------------------------------------------------------------*)
(* same as above, but using and abstract value `q0` rather than `q` *)

op q0 : index -> bool.
axiom q0p j : p j = q0 j.

global lemma _ : 
equiv(
  fun (j:index) => if p j then diff(n(i),a),
  if q0 jc then diff(n(i),a)
).
Proof.
crypto Random.
+ intro k k0 [Hl H Hl0 H0] Neq.
  have [A  | ?] // := Hl  k0 => {Hl}.
  have [A0 | ?] // := Hl0 k  => {Hl0}.
  have [] := total k k0.
  - smt.
  - rewrite /( > ). 
    smt.
  - smt.
+ intro k [H??]. 
  rewrite -q0p in *.
  admit. (* There is a precision issue here, as we are missing the
            fact that `not (p jc)`. This prevent us from concluding. *)
+ auto.
Qed.
