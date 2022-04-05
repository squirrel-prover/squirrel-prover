set autoIntro=false.
(* set debugConstr=true. *)

hash H
name k:message

channel c

name n:message
name m:message

name n1  : index -> message.
name n1p : index -> message.
name n2  : index -> index -> message.

name nt : timestamp -> index -> message.

system null.

abstract ok : message.
abstract ok2 : message.

(*------------------------------------------------------------------*)
(* system with one hash *)

system [u] (!_i U: out(c, H(<n1(i), ok>,k))).

system u2 = [u/left] with gprf time, H(_, k).

print system [u2].

(*------------------------------------------------------------------*)
(* system with two hashes *)

system [v] (!_i U: out(c, <H(n1(i), k), H(n2(i,i),k)>)).

system v2 = [v/left] with gprf time, H(_, k).

print system [v2].

(*------------------------------------------------------------------*)
(* system with two hashes in two actions *)

system [w] !_i ((U: out(c, H(n1(i), k) ) |
                 V: out(c, H(n2(i,i),k)) )).

system w2 = [w/left] with gprf time, H(_, k).

print system [w2].

(*------------------------------------------------------------------*)
(* system with one hash under binder (index) *)

system [t] (!_i U: out(c, seq(j : index -> H(n2(i,j),k)))).

system t2 = [t/left] with gprf time, H(_, k).

print system [t2].

(*------------------------------------------------------------------*)
(* system with one hash under binder (timestamp) *)

system [s] (!_i U: out(c, seq(t : timestamp -> H(nt(t,i),k)))).

system s2 = [s/left] with gprf time, H(_, k).

print system [s2].

(*------------------------------------------------------------------*)
(* system with two nested hashes and a global macro *)

system [p] (!_i U: let m = H(n1p(i),k) in out(c, m)).

system p2 = [p/left] with gprf time, H(_, k).

print system [p2].

(* TODO: there should be only two cases. Some redundancy here. *)

goal [p2/left] _ (i,j : index) : happens(U(i)) => m1(j)@U(i) = empty.
Proof.
  intro Hap.
  expand m1.
Abort.

(*------------------------------------------------------------------*)
(* system with two nested hashes and a global macro *)

system [q] (!_i U: let m = H(n1p(i),k) in out(c, H(<n1(i),m>,k))).

system q2 = [q/left] with gprf time, H(_, k).

print system [q2].

goal [p2/left] _ (i,j : index) : happens(U(i)) => m1(i)@U(i) = empty.
Proof.
  intro Hap.
  expand m1.
Abort.

(* TODO: generated condition is bugged. It should be t < U(i). 
   For global macros, we should use the timestamp variables in the global 
   data instead of a variable we build. 

   Also, rewrite the code to clarify that we do a different rewriting 
   for global and local macros. *)

(*------------------------------------------------------------------*)
(* system with two nested hashes *)

system [x] (!_i U: out(c, H(<n1(i),H(n2(i,i),k)>,k))).

system x2 = [x/left] with gprf time, H(_, k).

print system [x2].
(* TODO: hash not fully substituted ... *)

(* (*------------------------------------------------------------------*) *)
(* (* system with two nested hashes under binder (index) *) *)

(* system [y] (!_i U: out(c, seq(j : index -> H(<n1(j),H(n2(i,j),k)>,k)))). *)

(* system y2 = [y/left] with gprf time, H(_, k). *)

(* print system [y2]. *)
