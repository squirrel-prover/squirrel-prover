set autoIntro=false.
set debugTactics=true.

channel c

abstract ok : message

system [s1] in(c,x); let S=diff(<x,ok>,x) in A : out(c,S).

system [s2] in(c,x); let St=diff(x,<x,ok>) in A : out(c,St).

equiv [left:s1, right:s2] test.
Proof.
nosimpl(induction t).

auto.

expandall.
(* The output should simplify into <input@A,ok> or,
   equivalently, diff(<input@A,ok>,<input@A,ok>).
   The goal, where input macros expand to bi-terms,
   is correct: dup can be used. *)
fa 0; fa 1.
by fadup.
Qed.

equiv [left:s1, left:s1] test2.
Proof.
induction t.
auto.

expandall.
fa 0; fa 1; fa 2; fa 3.
(* The output should be <input@A,ok>. *)
by fadup.
Qed.

equiv [right:s2, left:s1] test3.
Proof.
induction t. 
auto.

expandall.
fa 0; fa 1; fa 2; fa 2; fa 3; fa 4.
(* The output should be <input@A,ok>. *)
by fadup.
Qed.

equiv [right:s1, right:s1] test4.
Proof.
induction t.
auto.

expandall.
(* The ouput should reduce to input@A. *)
by fa 0.
Qed.
