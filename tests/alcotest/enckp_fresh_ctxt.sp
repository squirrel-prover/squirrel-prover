senc enc,dec
name k1 : message
name k2 : message
name r : message
name n : message

system null.

equiv test : <r,enc(n,r,diff(k1,k2))>.
Proof.
  enckp 0.
Qed.
