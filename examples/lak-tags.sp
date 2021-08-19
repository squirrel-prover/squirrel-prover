(*******************************************************************************
LAK (WITH PAIRS)

[D] Lucca Hirschi, David Baelde, and Stéphanie Delaune. A method for
unbounded verification of privacy-type properties. Journal of Computer
Security, 27(3):277–342, 2019.

R --> T : nR
T --> R : <nT,h(<<nR,nT>,tag1>,kT)>
R --> T : h(<<h(<<nR,nT>,tag1>,kT),nR>,tag2>,kR)

We consider tags in the messages (tag1 and tag2) to ease the proof.

This is a "light" model without the last check of T.
*******************************************************************************)
set autoIntro=false.

hash h

abstract ok : message
abstract ko : message

abstract tag1 : message
abstract tag2 : message

name key : index->message
name key': index->index->message

channel cT
channel cR

process tag(i:index,k:index) =
  new nT;
  in(cR,nR);
  let m2 = h(<<nR,nT>,tag1>,diff(key(i),key'(i,k))) in
  out(cT,<nT,m2>)

process reader(j:index) =
  new nR;
  out(cR,nR);
  in(cT,x);
  if exists (i,k:index),
     snd(x) = h(<<nR,fst(x)>,tag1>,diff(key(i),key'(i,k)))
  then
    out(cR, try find i,k such that
              snd(x) = h(<<nR,fst(x)>,tag1>,diff(key(i),key'(i,k)))
            in
              h(<<snd(x),nR>,tag2>,diff(key(i),key'(i,k))))
  else
    out(cR,ko)

system ((!_j R: reader(j)) | (!_i !_k T: tag(i,k))).

axiom tags_neq : tag1 <> tag2.

goal wa_R1 (j:index):
  happens(R1(j)) =>
    (cond@R1(j)
     <=>
     (exists (i,k:index),
       T(i,k) < R1(j) && R(j) < T(i,k) &&
       snd(output@T(i,k)) = snd(input@R1(j)) &&
       fst(output@T(i,k)) = fst(input@R1(j)) &&
       input@T(i,k) = output@R(j))).
Proof.
  intro Hap.
  expand cond.
  split.

  (* COND => WA *)
  intro [i k H].
  use tags_neq; project.
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
  by expand output, m2. 
Qed.

goal wa_R2 (j:index):
  happens(R2(j)) =>
   (cond@R2(j)
    <=>
    (not(exists (i,k:index),
      T(i,k) < R2(j) && R(j) < T(i,k) &&
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
  by expand output, m2.
  
  (* COND => WA *)
  intro H [i k Meq].
  use H.
  use tags_neq; project. 
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

goal [left] wa_R1_left (i,j:index):
  happens(R1(j)) =>
    ((snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key(i)))
     <=>
     (exists k:index,
     T(i,k) < R1(j) && R(j) < T(i,k) &&
     snd(output@T(i,k)) = snd(input@R1(j)) &&
     fst(output@T(i,k)) = fst(input@R1(j)) &&
     input@T(i,k) = output@R(j))).
Proof.
  intro Hap.
  split; 2 : by intro [k _]; expand output, m2.

  intro Meq.
  use tags_neq.
  euf Meq => _ _ _ //.
  exists k.
  assert input@T(i,k)=nR(j) as Meq1; 1: auto.
  fresh Meq1 => C /=.
  case C => //. 
  by depends R(j),R2(j).
Qed.

goal [right] wa_R1_right (i,j,k:index):
  happens(R1(j)) =>
    ((snd(input@R1(j)) = h(<<nR(j),fst(input@R1(j))>,tag1>,key'(i,k)))
     <=>
     (T(i,k) < R1(j) && R(j) < T(i,k) &&
     snd(output@T(i,k)) = snd(input@R1(j)) &&
     fst(output@T(i,k)) = fst(input@R1(j)) &&
     input@T(i,k) = output@R(j))).
Proof.
  intro Hap.
  split; 2 : by intro [k _]; expand output, m2.

  intro Meq.
  use tags_neq.
  euf Meq => _ _ _ //.
  assert input@T(i,k)=nR(j) as Meq1; 1: auto.
  fresh Meq1 => C /=.
  case C => //. 
  by depends R(j),R2(j).
Qed.


equiv unlinkability.
Proof.
  induction t.

  (* init *)
  auto.

  (* Case R *)
  expand frame, exec, cond, output.
  fa 0; fa 1; fa 1.
  fresh 1; yesif 1.
  repeat split => // j0 H1. 
  by depends R(j0),R2(j0).
  by depends R(j0),R1(j0).
  auto.

  (* Case R1 *)
  expand frame, exec, output.
  fa 0; fa 1.

  equivalent
    cond@R1(j),
    (exists (i,k:index),
      T(i,k) < R1(j) && R(j) < T(i,k) &&
      snd(output@T(i,k)) = snd(input@R1(j)) &&
      fst(output@T(i,k)) = fst(input@R1(j)) &&
      input@T(i,k) = output@R(j)).
  by use wa_R1 with j.

  equivalent
    (if exec@pred(R1(j)) &&
        exists (i,k:index),
        (((T(i,k) < R1(j) && R(j) < T(i,k) && snd(output@T(i,k)) = snd(input@R1(j))) &&
        fst(output@T(i,k)) = fst(input@R1(j))) &&
        input@T(i,k) = output@R(j))
     then (try find i,k such that
             snd(input@R1(j)) =
             h(<<nR(j),fst(input@R1(j))>,tag1>,diff(key(i),key'(i,k)))
           in
             h(<<snd(input@R1(j)),nR(j)>,tag2>,diff(key(i),key'(i,k))))),
    (if exec@pred(R1(j)) &&
        exists (i,k:index),
        (T(i,k) < R1(j) && R(j) < T(i,k) && snd(output@T(i,k)) = snd(input@R1(j)) &&
        fst(output@T(i,k)) = fst(input@R1(j)) &&
        input@T(i,k) = output@R(j))
     then (try find i,k such that
            (exec@pred(R1(j)) &&
  	   (T(i,k) < R1(j) && snd(output@T(i,k)) = snd(input@R1(j)) &&
  	    fst(output@T(i,k)) = fst(input@R1(j)) &&
  	    R(j) < T(i,k) && input@T(i,k) = output@R(j)))
           in
  	   if exec@pred(R1(j))
  	   then h(<<snd(input@R1(j)),nR(j)>,tag2>,diff(key(i),key'(i,k))))).
  fa; 1,4: intro *; auto.
  intro [_ [i k _]] /=.
  by exists i,k. 
  intro [_ [i k _]] /=. 
  project.

  (* LEFT *)
  fa => // _.
  exists k => /=.
  use wa_R1_left with i0,j as [H1 H2]; 2: auto.
  clear H2.
  use H1 as [k1 _]; 2: auto. 
  clear H1. 
  by expand output, m2. 
  by yesif.

  (* RIGHT *)
  fa => // _.
  use wa_R1_right with i0,j,k0 as [H1 H2]; 2: auto.
  clear H2.
  use H1 as [k1 _]; 2: auto. 
  clear H1. 
  by expand output, m2. 
  by yesif.


  fa 2; fadup 1.
  fa 1; fadup 1.
  prf 1.
  ifcond 1, exec@pred(R1(j)); 1: auto.
  fa 1.
  yesif 1. 
  by use tags_neq; project.
  by fresh 1.

  (* Case R2 *)
  expand frame, exec, output.
  fa 0; fa 1.
  equivalent
    cond@R2(j),
    (not(exists (i,k:index),
      T(i,k) < R2(j) && R(j) < T(i,k) &&
      snd(output@T(i,k)) = snd(input@R2(j)) &&
      fst(output@T(i,k)) = fst(input@R2(j)) &&
      input@T(i,k) = output@R(j))).
  by use wa_R2 with j.
  by fadup 1.

  (* Case T *)
  expand frame, exec, cond, output.
  expand m2(i,k)@T(i,k).
  fa 0. fa 1. fa 1. fa 1. 
  prf 2.
  yesif 2; simpl.
  use tags_neq. 
  by project; repeat split; intro > _ _ [[_ Meq] _]; fresh Meq. 

  fresh 2.
  by fresh 1; yesif 1.
Qed.
