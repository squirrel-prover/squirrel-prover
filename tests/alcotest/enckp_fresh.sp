senc enc,dec
name k1 : message
name k2 : message
name r : message
name n : message

system null.

equiv test : enc(n,r,diff(k1,k2)), r.
Proof.
  enckp 0.
Qed.
