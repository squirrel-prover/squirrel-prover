(*******************************************************************************
HASH-LOCK

[C] Ari Juels and Stephen A. Weis. Defining strong privacy for RFID. ACM
Trans. Inf. Syst. Secur., 13(1):7:1–7:23, 2009.

R --> T : nR
T --> R : < nT, h(<nR,nT>,kT) >
R --> T : ok
*******************************************************************************)
set autoIntro=false.

hash h

abstract ok : message
abstract ko : message

name key : index->message
name key' : index->index->message
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

goal wa_R1 (j:index):
  happens(R1(j)) =>
    (cond@R1(j) <=>
     (exists (i,k:index), T(i,k) < R1(j) && R(j) < T(i,k) &&
       snd(output@T(i,k)) = snd(input@R1(j)) &&
       fst(output@T(i,k)) = fst(input@R1(j)) &&
       input@T(i,k) = output@R(j))).
Proof.
  intro Hap.
  expand cond.
  split.

  (* COND => WA *)
  intro [i k H].
  project.
  (* LEFT *)
  euf H => _ _ _ //.
  exists i,k0.
  assert input@T(i,k0)=nR(j) as Meq1; 1: auto.
  fresh Meq1 => C /=. 
  case C => //. 
  by depends R(j),R2(j).

  (* RIGHT *)
  euf H => _ _ _ //.
  exists i,k.
  assert input@T(i,k)=nR(j) as Meq1; 1: by auto.
  fresh Meq1 => C /=.
  case C => //. 
  by depends R(j),R2(j).

  (* WA => COND *)
  intro [i k _]; exists i,k. 
  by expand output. 
Qed.

goal wa_R2 (j:index):
  happens(R2(j)) =>
   (cond@R2(j) <=>
     (not(exists (i,k:index), T(i,k) < R2(j) && R(j) < T(i,k) &&
       snd(output@T(i,k)) = snd(input@R2(j)) &&
       fst(output@T(i,k)) = fst(input@R2(j)) &&
       input@T(i,k) = output@R(j)))).
Proof.
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
  case C => //. 
  by depends R(j),R1(j).

  (* RIGHT *)
  euf Meq => _ _ _ //.
  exists i,k.
  assert input@T(i,k)=nR(j) as Meq1; 1: auto.
  fresh Meq1 => C /=.
  case C => //. 
  by depends R(j),R1(j).
Qed.

equiv unlinkability.
Proof.
  induction t.

  (* init *)
  auto.

  (* Case R *)
  expand frame, exec, cond, output.
  fa 0. fa 1. fa 1.
  fresh 1;  yesif 1.
  repeat split => j0 _ //.
  by depends R(j0), R2(j0).
  by depends R(j0), R1(j0).
  auto.

  (* Case R1 *)
  expand frame, exec, output.
  fa 0. fa 1.
  equivalent
    cond@R1(j),
    (exists (i,k:index), T(i,k) < R1(j) && R(j) < T(i,k) &&
      snd(output@T(i,k)) = snd(input@R1(j)) &&
      fst(output@T(i,k)) = fst(input@R1(j)) &&
      input@T(i,k) = output@R(j)).
  by use wa_R1 with j.
  by fadup 1.

  (* Case R2 *)
  expand frame, exec, output.
  fa 0. fa 1.
  equivalent
    cond@R2(j),
    (not(exists (i,k:index), T(i,k) < R2(j) && R(j) < T(i,k) &&
      snd(output@T(i,k)) = snd(input@R2(j)) &&
      fst(output@T(i,k)) = fst(input@R2(j)) &&
      input@T(i,k) = output@R(j))).
  by use wa_R2 with j.
  by fadup 1.

  (* Case T *)
  expand frame, exec, cond, output.
  fa 0. fa 1. fa 1. fa 1.
  prf 2. yesif 2; simpl.
  project;
  repeat split => > _ _ [_ Meq0]; (try fresh Meq0); auto.

  fresh 2.
  by fresh 1; yesif 1. 
Qed.
