include Core.
include WeakSecrecy.
include Libs.
include Games.
include[admit] processes.

(* In the first phase of the protocol, Alice and Bob's votes are
   private thanks to the Commitment Hiding property. *)
global lemma voteHiding @system:Privacy_CCA :
  equiv(
    comm diff(v0, v1) diff(kc0, kc1),
    comm diff(v1, v0) diff(kc1, kc0),
    sk_mix1,
    sk_mix2,
    seedA_enc1,
    seedA_enc2,
    seedB_enc1,
    seedB_enc2,
    tkA,
    tkB,
    v0,
    v1,
    rdAdmin
  ).
Proof.
  trans 
     0: comm v1 kc0,
     1: comm v0 kc1; simpl ~diffr.
  crypto CommitmentHiding.  
  rewrite /v0 /v1.
  fa 2!comm _ _, 2!att' _. 
  fresh 1; 1: auto.
  fresh 2; 1: auto.
  refl.
Qed.
