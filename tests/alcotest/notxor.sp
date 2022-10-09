name m : message
name n : message
name k : message

abstract f : message * message -> message

system null.

equiv test : f(diff(n,m),k).
Proof.
  xor 0.
