set autoIntro=false.
set debugTactics=true.

channel c

abstract ok : message

system [s1] in(c,x); let S=diff(<x,ok>,x) in A : out(c,S).

system [s2] in(c,x); let St=diff(x,<x,ok>) in A : out(c,St).

equiv [left,s1] [right,s2] test.
Proof.
nosimpl(induction t).
simpl.
expand frame@A.
expand output@A.
expand S@A; expand St@A.
(* The output should simplify into <input@A,ok> or,
   equivalently, diff(<input@A,ok>,<input@A,ok>).
   The goal, where input macros expand to bi-terms,
   is correct: dup can be used. *)
nosimpl(fa 0; fa 1).
nosimpl(fadup).
expandall; fa 0; fa 1; assumption.
Qed.

equiv [left,s1] [left,s1] test2.
Proof.
induction t.
expandall.
nosimpl(fa 0; fa 1; fa 2; fa 3).
(* The output should be <input@A,ok>. *)
fadup.
Qed.

equiv [right,s2] [left,s1] test3.
Proof.
induction t; expandall.
nosimpl(fa 0; fa 1; fa 2; fa 2; fa 3; fa 4).
(* The output should be <input@A,ok>. *)
fadup.
Qed.

equiv [right,s1] [right,s1] test4.
Proof.
induction t.
expandall.
(* The ouput should reduce to input@A. *)
fa 0.
Qed.
