senc enc,dec
name k1 : message
name k2 : message
name r : message
name n : message

system null.

(* Should fail with Bad_ssc. *)
equiv fail (x:message) : enc(x,r,diff(k1,k2)).
Proof.
  enckp 0.
