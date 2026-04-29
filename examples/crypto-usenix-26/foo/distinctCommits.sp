(******************************************************************************
In this file, we prove that Alice and Bob's commits to their vote are
distinct thanks to the Commitment Hiding property. 

These lemmas are proved in the protocol obtained after idealizing the
encryptions (i.e. `Privacy_CCA`), as this is the system they will be
used in.

There are auxiliary results used during the deduction proof, to
characterize the mix-net state.

The main lemma is lemma `distinct_commit`.

*******************************************************************************)

include Core.
include NonDeduction.
include Libs.
include Games.
include[admit] processes.

name nf: message.



lemma diff_commL @set:Privacy_CCA/left @equiv:Privacy_CCA :
   happens Start =>
  cmA@Start <> cmB@Start.
Proof.
  intro Hap.
  have rew :( cmA@Start <> cmB@Start) = (comm v0 kc0  <> comm v1 kc1  ). auto.
  rewrite rew.  
  clear rew.
  ghave E : 
    equiv(
      diff(
       (comm v0 kc0  = comm v1 kc1  ),
       (comm nf kc0 = comm v1 kc1)) ). {
  crypto CommitmentHiding.
  }
  simpl.
  rewrite  -eq_false.
  rewrite eq_iff; split; 2:auto.
  intro H.
  rewrite equiv E.
  apply f_apply (fun x => copen x kc0) in H.
  rewrite !copen_comm /= in H.
  by  fresh H.
Qed.

lemma diff_commR @set:Privacy_CCA/right @equiv:Privacy_CCA :
   happens Start =>
  cmA@Start <> cmB@Start.
Proof.
  intro Hap.
  have rew :( cmA@Start <> cmB@Start) = (comm v0 kc0  <> comm v1 kc1  ). 
  rewrite neq_sym.
  auto.
  rewrite rew.  
  clear rew.
  ghave E : 
    equiv(
      diff(
       (comm nf kc0 = comm v1 kc1),  (comm v0 kc0  = comm v1 kc1  )) ). {
  crypto CommitmentHiding.
  }
  rewrite  -eq_false.
  rewrite eq_iff; split; 2:auto.
  intro H.
  rewrite equiv -E.
  apply f_apply (fun x => copen x kc0) in H.
  rewrite !copen_comm /= in H.
  by  fresh H.
Qed.


lemma distinct_commit @set:Privacy_CCA @equiv:Privacy_CCA :
  happens Start =>
  cmA@Start <> cmB@Start.
Proof. project; [1: apply diff_commL | 2: apply diff_commR]. Qed.
 
