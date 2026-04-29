(******************************************************************************
In this file, we prove that the encryptions Alice and Bob's send to
the mix-nets are almost always distinct using the IND-CCA2 property of
encryption.

These lemmas are proved in the protocol obtained after idealizing the
encryptions (i.e. `Privacy_CCA`), as this is the system they will be
used in.

There are auxiliary results used during the deduction proof, to
characterize the mix-net state.

The main lemmas are:
- Lemma `EncA1EncB1.diff_enc`, which shows that Alice and Bob's
   encryptions to the _first_ mix-net (i.e. `MVC`) are distinct.
- Lemma `EncA2EncB2.diff_enc`, which shows that Alice and Bob's
   encryptions to the _second_ mix-net (i.e. `MVP`) are distinct.
- Variants of the previous lemma that only apply to the left or right
  projections of the `Privacy_CCA` system. E.g. `EncA1EncB1.diff_encL`
  is `EncA1EncB1.diff_enc` restricted to `Privacy_CCA/left`.

*******************************************************************************)

include Core.
include NonDeduction.
include Libs.
include Games.
include[admit] processes.


type mess_len1[serializable,large].
type mess_len2[serializable,large].



axiom [any] len1 (n:mess_len1):
len zero_enc1 = len (format n).

axiom [any] len2 (n:mess_len2):
len zero_enc2 = len (format n).

exact axiom [any] format_mess_len1   (x : mess_len1) : read (format x) = x.
hint rewrite format_mess_len1.


exact axiom [any] format_mess_len2   (x : mess_len2) : read (format x) = x.
hint rewrite format_mess_len2.

(*------------------------------------------------------------------*)
namespace EncA.
  (* auxiliary name used in the proof below *)
  name nFresh : mess_len2.
  
  (* auxiliary lemma *)
  lemma not_emptyL @set:Privacy_CCA/left @equiv:Privacy_CCA :
    (empty = format (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2)) = false.
  Proof.
    rewrite eq_iff; split; 2:auto.
    intro H.
    ghave E : 
    equiv(diff (empty = format (encr zero_enc2   (pk_enc sk_mix2) seedA_enc2),
                empty = format (encr (format nFresh) (pk_enc sk_mix2) seedA_enc2))). {
    crypto CCA2. 
    by apply len2.
    }.
    rewrite equiv E.
    apply f_apply read[ctxt] in H. 
    rewrite format_encr in H. 
    apply f_apply (fun x => decr x sk_mix2) in H.
    rewrite decr_encr /= in H.
    apply f_apply read[mess_len2] in H.
    rewrite format_mess_len2 in H.
    by fresh H.
  Qed.

  (* auxiliary lemma: similar to the lemma above, but on the right *)
  lemma not_emptyR @set:Privacy_CCA/right @equiv:Privacy_CCA :
    (empty = format (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2)) = false.
  Proof.
    rewrite eq_iff; split; 2:auto.
    intro H.
    ghave E : 
    equiv(diff (empty = format (encr (format nFresh) (pk_enc sk_mix2) seedA_enc2),
                empty = format (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2))). {
    crypto CCA2.
    rewrite eq_sym.
    by apply len2.
    }.
    rewrite equiv -E.
    apply f_apply read[ctxt] in H. 
    rewrite format_encr in H. 
    apply f_apply (fun x => decr x sk_mix2) in H.
    rewrite decr_encr /= in H.
    apply f_apply read[mess_len2] in H.
    rewrite format_mess_len2 in H.
    by fresh H.
  Qed.

  lemma not_empty @set:Privacy_CCA @equiv:Privacy_CCA :
    (empty = format (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2)) = false.
  Proof. project; [1: apply not_emptyL | 2: apply not_emptyR]. Qed.
end EncA.

(*------------------------------------------------------------------*)
(* same as in `EncB.not_empty`, but for `seedB_enc2` rather than `seedA_enc2` *)
namespace EncB.
  (* auxiliary name used in the proof below *)
  name nFresh : mess_len2.
  
  (* auxiliary lemma *)
  lemma not_emptyL @set:Privacy_CCA/left @equiv:Privacy_CCA :
    (empty = format (encr zero_enc2 (pk_enc sk_mix2) seedB_enc2)) = false.
  Proof.
    rewrite eq_iff; split; 2:auto.
    intro H.
    ghave E : 
    equiv(diff (empty = format (encr zero_enc2   (pk_enc sk_mix2) seedB_enc2),
                empty = format (encr (format nFresh) (pk_enc sk_mix2) seedB_enc2))). {
    crypto CCA2.
    by apply len2.
    }.
    rewrite equiv E.
    apply f_apply read[ctxt] in H. 
    rewrite format_encr in H. 
    apply f_apply (fun x => decr x sk_mix2) in H.
    rewrite decr_encr /= in H.
    apply f_apply read[mess_len2] in H.
    rewrite format_mess_len2 in H.
    by fresh H.
  Qed.

  (* auxiliary lemma: similar to the lemma above, but on the right *)
  lemma not_emptyR @set:Privacy_CCA/right @equiv:Privacy_CCA :
    (empty = format (encr zero_enc2 (pk_enc sk_mix2) seedB_enc2)) = false.
  Proof.
    rewrite eq_iff; split; 2:auto.
    intro H.
    ghave E : 
    equiv(diff (empty = format (encr (format nFresh) (pk_enc sk_mix2) seedB_enc2),
                empty = format (encr zero_enc2   (pk_enc sk_mix2) seedB_enc2))). {
    crypto CCA2. 
    rewrite eq_sym.
    by apply len2.
    }.
    rewrite equiv -E.
    apply f_apply read[ctxt] in H. 
    rewrite format_encr in H. 
    apply f_apply (fun x => decr x sk_mix2) in H.
    rewrite decr_encr /= in H.
    apply f_apply read[mess_len2] in H.
    rewrite format_mess_len2 in H.
    by fresh H.
  Qed.

  lemma not_empty @set:Privacy_CCA @equiv:Privacy_CCA :
    (empty = format (encr zero_enc2 (pk_enc sk_mix2) seedB_enc2)) = false.
  Proof. project; [1: apply not_emptyL | 2: apply not_emptyR]. Qed.
end EncB.


(*------------------------------------------------------------------*)
namespace EncA1EncB1.
  (* auxiliary name used in the proof below *)
  name nFresh : mess_len1.
  
  (* auxiliary lemma *)
  lemma diff_encL @set:Privacy_CCA/left @equiv:Privacy_CCA :
    (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1 = 
     encr zero_enc1 (pk_enc sk_mix1) seedB_enc1  ) = false.
  Proof.
    rewrite eq_iff; split; 2:auto.
    intro H.
    ghave E : 
    equiv(
      diff(
       (encr zero_enc1   (pk_enc sk_mix1) seedA_enc1 = 
        encr zero_enc1   (pk_enc sk_mix1) seedB_enc1  ),
       (encr (format nFresh) (pk_enc sk_mix1) seedA_enc1 = 
        encr zero_enc1   (pk_enc sk_mix1) seedB_enc1  )
      )
    ). {
      crypto CCA2. 
      apply len1.
    }.
    rewrite equiv E.
    apply f_apply (fun x => decr x sk_mix1) in H.
    rewrite !decr_encr /= in H.
    apply f_apply read[mess_len1] in H.
    rewrite format_mess_len1 in H.
    by fresh H.
  Qed.

  (* auxiliary lemma: similar to the lemma above, but on the right *)
  lemma diff_encR @set:Privacy_CCA/right @equiv:Privacy_CCA :
    (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1 = 
     encr zero_enc1 (pk_enc sk_mix1) seedB_enc1  ) = false.
  Proof.
    rewrite eq_iff; split; 2:auto.
    intro H.
    ghave E : 
    equiv(
      diff(
       encr (format nFresh) (pk_enc sk_mix1) seedA_enc1 = 
       encr zero_enc1   (pk_enc sk_mix1) seedB_enc1,
       encr zero_enc1   (pk_enc sk_mix1) seedA_enc1 = 
       encr zero_enc1   (pk_enc sk_mix1) seedB_enc1
     )
    ). {
    crypto CCA2.
    rewrite eq_sym. 
    apply len1.
    }.
    rewrite equiv -E.
    apply f_apply (fun x => decr x sk_mix1) in H.
    rewrite !decr_encr /= in H.
    apply f_apply read[mess_len1] in H.
    rewrite format_mess_len1 in H.
    by fresh H.
  Qed.

  lemma diff_enc @set:Privacy_CCA @equiv:Privacy_CCA :
    (encr zero_enc1 (pk_enc sk_mix1) seedA_enc1 = 
     encr zero_enc1 (pk_enc sk_mix1) seedB_enc1  ) = false.
  Proof. project; [1: apply diff_encL | 2: apply diff_encR]. Qed.
end EncA1EncB1.

(*------------------------------------------------------------------*)
(* same as `EncA1EncB1`, but for the second round of encryptions *)
namespace EncA2EncB2.
  (* auxiliary name used in the proof below *)
  name nFresh : mess_len2.
  
  (* auxiliary lemma *)
  lemma diff_encL @set:Privacy_CCA/left @equiv:Privacy_CCA :
    (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2 = 
     encr zero_enc2 (pk_enc sk_mix2) seedB_enc2  ) = false.
  Proof.
    rewrite eq_iff; split; 2:auto.
    intro H.
    ghave E : 
    equiv(
      diff(
       (encr zero_enc2   (pk_enc sk_mix2) seedA_enc2 = 
        encr zero_enc2   (pk_enc sk_mix2) seedB_enc2  ),
       (encr (format nFresh) (pk_enc sk_mix2) seedA_enc2 = 
        encr zero_enc2   (pk_enc sk_mix2) seedB_enc2  )
      )
    ). {
    crypto CCA2. 
    apply len2.
    }.
    rewrite equiv E.
    apply f_apply (fun x => decr x sk_mix2) in H.
    rewrite !decr_encr /= in H.
    apply f_apply read[mess_len2] in H.
    rewrite format_mess_len2 in H.
    by fresh H.
  Qed.

  (* auxiliary lemma: similar to the lemma above, but on the right *)
  lemma diff_encR @set:Privacy_CCA/right @equiv:Privacy_CCA :
    (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2 = 
     encr zero_enc2 (pk_enc sk_mix2) seedB_enc2  ) = false.
  Proof.
    rewrite eq_iff; split; 2:auto.
    intro H.
    ghave E : 
    equiv(
      diff(
       encr (format nFresh) (pk_enc sk_mix2) seedA_enc2 = 
       encr zero_enc2   (pk_enc sk_mix2) seedB_enc2,
       encr zero_enc2   (pk_enc sk_mix2) seedA_enc2 = 
       encr zero_enc2   (pk_enc sk_mix2) seedB_enc2
     )
    ). {
    crypto CCA2. 
    rewrite eq_sym.
    apply len2.
    }.
    rewrite equiv -E.
    apply f_apply (fun x => decr x sk_mix2) in H.
    rewrite !decr_encr /= in H.
    apply f_apply read[mess_len2] in H.
    rewrite format_mess_len2 in H.
    by fresh H.
  Qed.

  lemma diff_enc @set:Privacy_CCA @equiv:Privacy_CCA :
    (encr zero_enc2 (pk_enc sk_mix2) seedA_enc2 = 
     encr zero_enc2 (pk_enc sk_mix2) seedB_enc2  ) = false.
  Proof. project; [1: apply diff_encL | 2: apply diff_encR]. Qed.
end EncA2EncB2.
