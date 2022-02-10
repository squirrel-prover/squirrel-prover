(*******************************************************************************
HASH-LOCK

[C] Ari Juels and Stephen A. Weis. Defining strong privacy for RFID. ACM
Trans. Inf. Syst. Secur., 13(1):7:1–7:23, 2009.

R --> T : nR
T --> R : < nT, h(<nR,nT>,kT) >
R --> T : ok
*******************************************************************************)
set autoIntro=false.
set postQuantumSound=true.

hash h

abstract ok : message
abstract ko : message

name key  : index          -> message
name key' : index -> index -> message

channel cT
channel cR

process tag(i:index,k:index) =
  new nT;
  in(cR,nR);
  out(cT,<nT,h(<nR,nT>,diff(key(i),key'(i,k)))>)

process reader(j:index) =
  new nR;
  out(cR,nR);
  in(cT,x);
  if exists (i,k:index), snd(x) = h(<nR,fst(x)>,diff(key(i),key'(i,k))) then
    out(cR,ok)
  else
    out(cR,ko)

system ((!_j R:reader(j)) | (!_i !_k T: tag(i,k))).

include Basic.

(* for the sack of simplicity, we assume injective pairing *)
axiom injective_pairing (x,y : message) :
  fst (x) = fst (y) => snd (x) = snd (y) => x = y.

goal wa_R1 (j:index):
  happens(R1(j)) =>
    (cond@R1(j) =
     (exists (i,k:index), T(i,k) < R1(j) && R(j) < T(i,k) &&
       output@T(i,k) = input@R1(j) &&
       input@T(i,k) = output@R(j))).
Proof.
  rewrite eq_iff.
  intro Hap.
  expand cond.
  split.

  (* COND => WA *)
  intro [i k H].
  project.
  (* LEFT *)
  euf H => _ _ _ //.
  exists i,k0.
  simpl.
  assert input@T(i,k0)=nR(j) as Meq1 by auto.
  fresh Meq1 => C /=.
  case C => //=;
  2: depends R(j),R2(j) by auto.
    by apply injective_pairing.
    intro _ /=.
    by apply injective_pairing.

  (* RIGHT *)
  euf H => _ _ _ //.
  exists i,k.
  assert input@T(i,k)=nR(j) as Meq1; 1: by auto.
  fresh Meq1 => C /=.
  case C => //=;
  2: depends R(j),R2(j) by auto.
    by apply injective_pairing.
    intro _ /=.
    by apply injective_pairing.

  (* WA => COND *)
  intro [i k _]; exists i,k.
  by expand output.
Qed.

goal wa_R2 (j:index):
  happens(R2(j)) =>
   (cond@R2(j) =
     (not(exists (i,k:index), T(i,k) < R2(j) && R(j) < T(i,k) &&
       output@T(i,k) = input@R2(j) &&
       input@T(i,k) = output@R(j)))).
Proof.
  rewrite eq_iff.
  intro Hap.
  expand cond.
  split.

  (* WA => COND *)
  intro H [i k H0].
  use H.
  exists i,k.
  by expand output.

  (* COND => WA *)
  intro H [i k Meq].
  use H.
  project.
  (* LEFT *)
  euf Meq => _ _ _ //.
  exists i,k0.
  assert input@T(i,k0)=nR(j) as Meq1; 1: auto.
  fresh Meq1 => C /=.
  case C => //=;
  2: depends R(j),R1(j) by auto.
    by apply injective_pairing.
    intro _ /=.
    by apply injective_pairing.

  (* RIGHT *)
  euf Meq => _ _ _ //.
  exists i,k.
  assert input@T(i,k)=nR(j) as Meq1; 1: auto.
  fresh Meq1 => C /=.
  case C => //=;
  2: depends R(j),R1(j) by auto.
    by apply injective_pairing.
    intro _ /=.
    by apply injective_pairing.
Qed.


equiv unlinkability.
Proof.
  induction t.

  (* init *)
  auto.

  (* Case R *)
  expand frame, exec, cond, output.
  fa 0; fa 1; fa 1.
  fresh 1; rewrite if_true.
  repeat split => j0 _ //.
  by depends R(j0), R2(j0).
  by depends R(j0), R1(j0).
  auto.

  (* Case R1 *)
  expand frame, exec, output.
  fa 0; fa 1.
  rewrite wa_R1 //.
  by fadup 1.

  (* Case R2 *)
  expand frame, exec, output.
  fa 0; fa 1.
  rewrite wa_R2 //.
  by fadup 1.

  (* Case T *)
  expand frame, exec, cond, output.
  fa 0; fa 1; fa 1; fa 1.
  prf 2.
  rewrite if_true /=.
  project;
  repeat split => > _ _ [_ Meq0]; (try fresh Meq0); auto.

  fresh 2.
  by fresh 1; rewrite if_true.
Qed.


(*-------------------------------------------------------------------*)
(* In the real-world system, we go further and prove injective
   authentication.  *)
goal [default/left] injective_auth (j:index):
  happens(R1(j)) =>
  cond@R1(j) =>
    (exists (i,k:index), R(j) < T(i,k) && T(i,k) < R1(j) &&
      output@T(i,k) = input@R1(j) &&
      input@T(i,k) = output@R(j) &&
      (forall (j0:index),
         happens(R1(j0)) =>
         cond@R1(j0) =>
         output@T(i,k) = input@R1(j0) =>
         input@T(i,k) = output@R(j0) =>
         j = j0
      )
    ).
Proof.
  intro Hap Cond.
  rewrite wa_R1 // in Cond.
  revert Cond => [i k [Clt Clt0 Cond0 Cond1]].
  exists i, k => /=.

  intro j0 => Cond_j0 Hap_j0 Cond0_j0 Cond1_j0.
  rewrite Cond1_j0 in Cond1.
  depends R(j0),R1(j0) by auto.
  intro _; rewrite /output in Cond1.
  by fresh Cond1.
Qed.
