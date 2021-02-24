set autoIntro=false.

abstract ok : message
abstract ko : message

abstract f : message->message

name n : message
name m : message
name k : message

system null.

axiom len_ko_n : len(ko XOR n) = len(k)
axiom len_ko_m : len(ko XOR m) = len(k).

equiv testXorOneArg : diff(f(ok),f(ok)),diff(n,m) XOR k.
Proof.
  nosimpl(xor 1).
  nosimpl(yesif 1).
  namelength k,n; namelength k,m.
  by auto.
  simpl.
Qed.

equiv testXorTwoArg : diff(f(ok),f(ok)),diff(ko,ko) XOR diff(n,m) XOR k.
Proof.
  nosimpl(xor 1, k).
  nosimpl(yesif 1).
  use len_ko_n; use len_ko_m.
  simpl.
Qed.
