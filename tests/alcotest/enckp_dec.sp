senc enc,dec
name k1 : message
name k2 : message
name r : message
name n : message
abstract ok : message

system null.

equiv fail (x:message) : dec(enc(n,r,diff(k1,k2)),k1).
Proof.
  try enckp enc(n,r,diff(k1,k2)).
Qed.
