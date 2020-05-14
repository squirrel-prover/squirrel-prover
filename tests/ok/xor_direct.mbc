abstract ok : message
abstract ko : message

abstract f : message->message

name n : message
name m : message
name k : message

axiom len_ko_n : len(ko XOR n) = len(k)
axiom len_ko_m : len(ko XOR m) = len(k)

system null.

equiv testXorOneArg : diff(f(ok),f(ok)),diff(n,m) XOR k.
Proof.
  nosimpl(xor 1).
  nosimpl(yesif 1).
  namelength k,n; namelength k,m.
  simpl.
Qed.

equiv testXorTwoArg : diff(f(ok),f(ok)),diff(ko,ko) XOR diff(n,m) XOR k.
Proof.
  nosimpl(xor 1, k).
  nosimpl(yesif 1).
  apply len_ko_n; apply len_ko_m.
  simpl.
Qed.
