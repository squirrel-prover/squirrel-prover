

include Basic.

channel c

abstract a : message
abstract b : message
abstract d : message

abstract f : message -> message
abstract g : message -> message -> message

op g2 (x : message) = g(x,x).

axiom [any] foo : a = b.
axiom [any] bar (x : message) : f(x) = x.

abstract check : message -> boolean

axiom [any] barP (x : message) : check(x) => f(x) = x.

(*------------------------------------------------------------------*)
system [Q] !_i (in(c,x); A: out(c, a)).

system Q1 = [Q/left] with rewrite foo.

goal [Q1] _ (i : index) :  
  happens(A(i)) => output@A(i) = b.
Proof.
  auto.
Qed.

(*------------------------------------------------------------------*)
axiom [any] check_ax0 : check(f(a)).
axiom [any] check_ax1 : check(a).

system [E] !_i (in(c,x); A: out(c, f(f(a)))).

system E1 = [E/left] with rewrite !barP foo.
Proof. by have ? := check_ax0. Qed.
Proof. by have ? := check_ax1. Qed.

goal [E1] _ (i : index) :  
  happens(A(i)) => output@A(i) = b.
Proof.
  auto.
Qed.

(*------------------------------------------------------------------*)
system [P] !_i (in(c,x); A: out(c, g2(x))).

system P1 = [P/left] with rewrite /g2.

goal [P1] _ (i : index) :  
  happens(A(i)) => output@A(i) = g(input@A(i),input@A(i)).
Proof.
  intro H. 
  rewrite /output.
  rewrite (eq_refl (g(input@A(i),input@A(i)))).
  assumption.
Qed.


(*------------------------------------------------------------------*)
system [R] !_i (in(c,x); A: out(c, f(f(f(g(a,d)))))).

system R1 = [R/left] with rewrite ?bar foo.

goal [R1] _ (i : index) :  
  happens(A(i)) => output@A(i) = g(b,d).
Proof.
  auto.
Qed.

(*------------------------------------------------------------------*)
name n : index -> message.

system [G] !_i (in(c,x); A: out(c, f(f(n(i))))).

axiom [G] check_ax_n0 (i : index) : happens (A(i)) => check(f(n(i))).
axiom [G] check_ax_n1 (i : index) : happens (A(i)) => check(n(i)).

system G1 = [G/left] with rewrite !barP foo.
Proof. by have ? := check_ax_n0 i. Qed.
Proof. by have ? := check_ax_n1 i. Qed.

goal [G1] _ (i : index) :  
  happens(A(i)) => output@A(i) = n(i).
Proof. 
  auto.
Qed.

(*------------------------------------------------------------------*)
system [H] !_i (in(c,x); let y = <x, zero> in A: out(c, y)).

system H1 = [H/left] with rewrite /y.

goal [H1] _ (i : index) :  
  happens(A(i)) => output@A(i) = <input@A(i), zero>. 
Proof. 
  intro Hap @/output. 
  rewrite eq_refl.
  assumption.
Qed.
