

name n : message
name m : message
name k : message

system null.

equiv test : diff(k,m) XOR n.
Proof.
  xor 0, k. (* name k is not XORed on both sides *)
