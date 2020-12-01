aenc enc,dec,pk
name k1 : message
name k2 : message
name r : message
name n : message
abstract ok : message

system null.

equiv test : enc(n,r,pk(diff(k1,k2))).
Proof.
  enckp 0.
Qed.

equiv test' : enc(n,r,diff(pk(k1),pk(k2))).
Proof.
  enckp 0.
Qed.

equiv test_arg1 : enc(n,r,pk(diff(k1,k2))).
Proof.
  enckp 0, enc(n,r,pk(diff(k1,k2))).
Qed.

equiv test_arg2 : enc(n,r,pk(diff(k1,k2))).
Proof.
  enckp 0, k2.
Qed.

equiv test_arg3 : enc(n,r,pk(diff(k1,k2))).
Proof.
  enckp 0, enc(n,r,pk(diff(k1,k2))), k2.
Qed.

equiv test_arg4 : enc(n,r,pk(diff(k1,k2))).
Proof.
  enckp 0, diff(k2,k1).
  enckp 0.
Qed.

equiv test_ctxt : <enc(n,r,pk(diff(k1,k2))),ok>.
Proof.
  nosimpl(enckp 0).
  auto.
  (* Decompose explicitly to make sure the context
   * is still there. *)
  nosimpl(fa 0). nosimpl(fa 0). fa 3.
Qed.

equiv test_diffsimpl : enc(n,r,pk(diff(k1,k1))).
Proof.
  (* It used to be impossible to apply enckp
   * because the diff is simplified away.
   * Now it is possible (although not natural)
   * to apply it by specifying the target. *)
  enckp 0, enc(n,r,pk(k1)).
Qed.

equiv test_diffsimpl_ctxt : <enc(n,r,pk(diff(k1,k1))),ok>.
Proof.
  (* TODO surprisingly enckp finds a suitable target,
   * unlike in test_diffsimpl. *)
  nosimpl(enckp 0).
  auto.
  (* Decompose explicitly to make sure the context
   * is still there. *)
  nosimpl(fa 0). nosimpl(fa 0). fa 3.
Qed.
