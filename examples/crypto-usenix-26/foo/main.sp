include Core.
include WeakSecrecy.
include Libs.
include Games.
include[admit] processes.
include[admit] cca.
include[admit] reduction.

global theorem vote_privacy @system:Privacy_real : equiv(frame@MOP).
Proof.
  have Hap : happens(MVP,MOP,BBS) by
    use Trace.happens_MVP;
    use Trace.happens_MOP;
    use Trace.happens_BBS.
  trans [Privacy_CCA].
  + trans [set:Privacy_real/left, Privacy_CCA/left;
           equiv:(Privacy_real/left, Privacy_CCA/left)];
      1,3 : refl.
    have h := (rewrite_cca_left MOP).
    by apply h.
  + by apply reduction_full.
  + sym.
    trans [set:Privacy_real/right, Privacy_CCA/right;
           equiv:(Privacy_real/right, Privacy_CCA/right)];
       1,3 : refl.
    have h := (rewrite_cca_right MOP).
    by apply h.
Qed.
