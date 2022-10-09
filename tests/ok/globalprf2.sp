
(* set debugConstr=true. *)

hash H
name k:message

channel c

name n:message
name m:message

name n1  : index -> message.
name n1p : index -> message.
name n2  : index * index -> message.

name nt : timestamp * index -> message.

system null.

abstract ok : message.
abstract ok2 : message.

(*------------------------------------------------------------------*)
(* system with one hash *)

system [u] (!_i U: out(c, H(<n1(i), ok>,k))).

system u2 = [u/left] with gprf time, H(_, k).

print system [u2].

(*------------------------------------------------------------------*)
(* system with two hashes in two actions *)

system [w] !_i ((U: out(c, H(n1(i), k) ) |
                 V: out(c, H(n2(i,i),k)) )).

system w2 = [w/left] with gprf time, H (_, k).

print system [w2].

(*------------------------------------------------------------------*)
(* system with one hash under binder (index) *)

system [t] (!_i U: out(c, seq(j : index => H(n2(i,j),k)))).

system t2 = [t/left] with gprf time, H(_, k).

print system [t2].

goal [t2] _ (i : index) : 
  happens(U(i)) => 
  output@U(i) = 
    seq(j:index =>
      (try find t:timestamp such that
         (exists (i0,j0:index),
            (t = U(i0)) && 
            ((t < U(i)) || ((t = U(i)) && (j0 < j))) &&
            (n2(i,j) = n2(i0,j0)))
       in
         try find i0,j0:index such that
           (t = U(i0)) && 
           ((t < U(i)) || ((t = U(i)) && (j0 < j))) && 
           (n2(i,j) = n2(i0,j0))
         in n_PRF3(i0,j0) else error2 else n_PRF3(i,j))).
Proof.
  intro Hap @/output. 
  auto.
Qed.


(*------------------------------------------------------------------*)
(* system with one hash under binder (timestamp) *)

system [s] (!_i U: out(c, seq(t : timestamp => H(nt(t,i),k)))).

system s2 = [s/left] with gprf time, H(_, k).

print system [s2].

(*------------------------------------------------------------------*)
(* system with two nested hashes and a global macro *)

system [p] (!_i U: let m = H(n1p(i),k) in out(c, m)).

system p2 = [p/left] with gprf time, H(_, k).

print system [p2].

goal [p2] _ (i : index) : 
  happens(U(i)) => 
  m1(i)@U(i) = 
  (try find t:timestamp such that
    (exists (i0:index), ((t = U(i0)) && (t < U(i)) && (n1p(i) = n1p(i0))))
     in
     try find i0:index such that
    ((t = U(i0)) && (t < U(i)) && (n1p(i) = n1p(i0)))
     in n_PRF5(i0) else error4 else n_PRF5(i)).
Proof. intro Hap @/m1. congruence. Qed.

(*------------------------------------------------------------------*)
(* system with two nested hashes and a global macro *)

system [q] (!_i U: let mq = H(n1p(i),k) in out(c, H(n1(i),k))).

system q2 = [q/left] with gprf time, H(_, k).

print system [q2].

goal [q2] _ (i : index) : 
  happens(U(i)) => 
  output@U(i) = 
  (try find t:timestamp such that
     ((exists (i0:index), ((t = U(i0)) && (t <= U(i)) && (n1(i) = n1p(i0)))) ||
      exists (i0:index),
        ((t = U(i0)) && (t < U(i)) && (n1(i) = n1(i0))))
   in
     try find i0:index such that
       ((t = U(i0)) && (t <= U(i)) && (n1(i) = n1p(i0)))
     in n_PRF7(i0)
     else
       try find i0:index such that
         ((t = U(i0)) && (t < U(i)) && (n1(i) = n1(i0)))
       in n_PRF6(i0) else error5 else n_PRF6(i)).
Proof.
  intro Hap @/output.
  auto.
Qed.

goal [q2] _ (i : index) : 
  happens(U(i)) => 
  mq(i)@U(i) = 
  (try find t:timestamp such that
     ((exists (i0:index), ((t = U(i0)) && (t < U(i)) && (n1p(i) = n1p(i0)))) ||
      exists (i0:index), ((t = U(i0)) && (t < U(i)) && (n1p(i) = n1(i0))))
   in
     try find i0:index such that
       ((t = U(i0)) && (t < U(i)) && (n1p(i) = n1p(i0)))
     in n_PRF7(i0)
     else
       try find i0:index such that
         ((t = U(i0)) && (t < U(i)) && (n1p(i) = n1(i0)))
       in n_PRF6(i0) else error5 else n_PRF7(i)).
Proof.
  intro Hap @/mq. 
  auto.
Qed.


(* The following system are not allowed, as they ave several hashes in the 
   same macros. *)
(* (*------------------------------------------------------------------*) *)
(* (* system with two hashes *) *)

(* system [v] (!_i U: out(c, <H(n1(i), k), H(n2(i,i),k)>)). *)

(* system v2 = [v/left] with gprf time, H(_, k). *)

(* print system [v2]. *)
