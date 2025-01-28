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


global lemma _ : 
equiv((fun (j:message) => diff(n(i),a))).
Proof.
checkfail crypto Random exn Failure.
Abort.


global lemma _ : 
equiv((fun (j:index) => diff(n(i),a)), diff(n(i),a)).
Proof.
crypto Random.
intro k k0.
intro [H H0].
intro Neq.
by have min := min_index k0 k H0 H.
Qed.
