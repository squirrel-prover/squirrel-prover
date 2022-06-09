

channel cR
channel cT

senc enc,dec

name n : message
name r : message
name k : message

system null.
goal ssenc : dec(enc(n,r,k),k) = n.
Proof.
auto.
Qed.
