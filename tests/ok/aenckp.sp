aenc enc,dec,pk
name k1 : message
name k2 : message
name r : message
name n : message
abstract ok : message

system null.

equiv test : enc(n,r,pk(diff(k1,k2))).
Proof.
  by enckp 0.
Qed.

equiv test' : enc(n,r,diff(pk(k1),pk(k2))).
Proof.
  by enckp 0.
Qed.

equiv test_arg1 : enc(n,r,pk(diff(k1,k2))).
Proof.
  by enckp 0, enc(n,r,pk(diff(k1,k2))).
Qed.

equiv test_arg2 : enc(n,r,pk(diff(k1,k2))).
Proof.
  by enckp 0, k2.
Qed.

equiv test_arg3 : enc(n,r,pk(diff(k1,k2))).
Proof.
  by enckp 0, enc(n,r,pk(diff(k1,k2))), k2.
Qed.

equiv test_arg4 : enc(n,r,pk(diff(k1,k2))).
Proof.
  enckp 0, diff(k2,k1). 
  auto.
  by enckp 0.
Qed.

equiv test_ctxt : <enc(n,r,pk(diff(k1,k2))),ok>.
Proof.
  nosimpl(enckp 0).
  auto.
  (* Decompose explicitly to make sure the context
   * is still there. *)
  nosimpl(fa 0). 
  nosimpl(fa 0). 
  by fa 3.
Qed.

equiv test_diffsimpl : enc(n,r,pk(diff(k1,k1))).
Proof.
  by enckp 0.
Qed.

equiv test_diffsimpl_ctxt : <enc(n,r,pk(diff(k1,k1))),ok>.
Proof.
  nosimpl(enckp 0).
  auto.
  (* Decompose explicitly to make sure the context
   * is still there. *)
  nosimpl(fa 0). nosimpl(fa 0). fa 3.
  auto.
Qed.
