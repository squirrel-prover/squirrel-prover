(*******************************************************************************
YPLRK05

T. van Deursen and S. Radomirović, ‘Attacks on RFID Protocols’,
Cryptology ePrint Archive, vol. 2008, no. 310, pp. 1–56, Aug. 2009.

The reader and tag share secrets k, k1, k2.
The reader initiates the protocol by challenging the tag with a nonce r1.
The tag responds with h(k1 XOR r1 XOR k).
The reader then replies with h(k2) and both tag and reader update secrets k1 and
k2.

R -> T : r1
T -> R : h(kT1+r1+k)
         kT1 := k1+h(k2)
         kT2 := k2+h(k1+r1+k)
R -> T : h(kR2)
         kR1 := k1+h(k2)
         kR2 := k2+h(k1+r1+k)

COMMENTS
- In this model we use 2 different keyed hash functions, instead of a single 
(not keyed) hash function as in the specification.

PROOFS 
- lastUpdateTag
- authentication
*******************************************************************************)

set autoIntro = false.

hash h1
hash h2

abstract ok : message
abstract error : message

name key1 : index->message
name key2 : index->message
name k : index->message
name r1 : index->message

name k1init : index->message
name k2init : index->message

mutable kT(i:index) : message = <k1init(i),k2init(i)>
mutable kR(ii:index) : message = <k1init(ii),k2init(ii)>

channel cT
channel cR

(* i = tag's identity, j = tag's session for identity i *)
process tag(i:index,j:index) =
  in(cR, xr1);
  out(cT, h1(fst(kT(i)) XOR xr1 XOR k(i), key1(i)));
  in(cR, xh2);
  if xh2 = h2(snd(kT(i)), key2(i)) then
    kT(i) := < fst(kT(i)) XOR h2(snd(kT(i)), key2(i)),
               snd(kT(i)) XOR h1(fst(kT(i)) XOR xr1 XOR k(i), key1(i)) >;
    out(cT, ok)
  else
    out(cT, error)

(* jj = generic reader's session *)
process reader(jj:index) =
  out(cR, r1(jj));
  in(cT, xh1);
  try find ii such that xh1 = h1(fst(kR(ii)) XOR r1(jj) XOR k(ii), key1(ii)) in
    let m = h2(snd(kR(ii)),key2(ii)) in
    kR(ii) := < fst(kR(ii)) XOR h2(snd(kR(ii)), key2(ii)),
                snd(kR(ii)) XOR h1(fst(kR(ii)) XOR r1(jj) XOR k(ii), key1(ii)) >;
    out(cT, m)
  else
    out(cT, error)

system ((!_jj R: reader(jj)) | (!_i !_j T: tag(i,j))).

(* Minimal sequentiality assumption needed for the proofs *)
axiom sequentiality:
  forall (t:timestamp) forall (i,j:index),
    happens(T(i,j),t,T1(i,j)) =>
    (T(i,j) < t && t < T1(i,j) => not(exists (j':index), t = T1(i,j') && j <> j')).

goal lastUpdateTag :
  forall (t:timestamp), forall (i,j:index), 
    happens(T(i,j),t,T1(i,j)) =>
      (t >= T(i,j) && t < T1(i,j)) => kT(i)@T(i,j) = kT(i)@t.
Proof.
  induction.
  intro t IH0 i j Hap [H1 H2].
  case t; intro He; simpl_left.
  by auto.
  by use IH0 with pred(R(jj)),i,j as H0.
  by use IH0 with pred(R1(jj,ii)),i,j as H0.
  by use IH0 with pred(R2(jj)),i,j as H0.

  subst t,T(i0,j0).
  assert T(i0,j0) = T(i,j) || T(i0,j0) > T(i,j) as H0.
  by eqtrace.
  case H0.
  by auto.
  by use IH0 with pred(T(i0,j0)),i,j.

  subst t,T1(i0,j0).
  assert i=i0 || i<>i0 as H0.
  by eqtrace.
  case H0.
  assert j=j0 || j<>j0 as H0.
  by eqtrace.
  case H0.
  (* case i=i0 && j=j0 *)
  by auto.
  (* case i=i0 && j<>j0 *)
  use sequentiality with T1(i,j0),i,j; 1,2: by auto.
  exists j0; by auto.
  (* case i<>i0 *)
  use IH0 with pred(T1(i0,j0)),i,j as Meq; 2,3,4: by auto.
  assert kT(i)@T1(i0,j0) = kT(i)@pred(T1(i0,j0)).
  by case (if i = i0 then
         <xor(fst(kT(i0)@pred(T1(i0,j0))),
              h2(snd(kT(i0)@pred(T1(i0,j0))),key2(i0))),
          xor(snd(kT(i0)@pred(T1(i0,j0))),
              h1(xor(xor(fst(kT(i0)@pred(T1(i0,j0))),input@T(i0,j0)),k(i0)),
                 key1(i0)))>
         else kT(i)@pred(T1(i0,j0))).
  by congruence.

  subst t,T2(i0,j0).
  by use IH0 with pred(T2(i0,j0)),i,j as H0.
Qed.

goal auth_R1_induction :
  forall (t:timestamp), forall (jj,ii:index),
    happens(R1(jj,ii)) =>
      ((t = R1(jj,ii) && exec@t) (* exec@t (not only cond@t) is needed *)
      =>
      (exists (j:index), T(ii,j) < t && output@T(ii,j) = input@t)).
Proof.
  induction. 
  intro t IH0 jj ii Hap [Ht Hexec].
  subst t,R1(jj,ii).
  expand exec@R1(jj,ii). expand cond@R1(jj,ii).
  destruct Hexec as [H1 Meq].
  euf Meq.

    (* case 1/3: equality with hashed message in update@R1 *)
    intro Ht Heq *.
    executable pred(R1(jj,ii)); 1,2: by auto.
    intro H.
    use H with R1(jj0,ii) as Ht1; 2: by auto.
    expand exec@R1(jj0,ii). expand cond@R1(jj0,ii).
    destruct Ht1 as [H2 Meq'].
    use IH0 with R1(jj0,ii),jj0,ii; 2,3,4: by auto.
    simpl_left.
    exists j.
    split.
    by auto.
    by congruence.  

    (* case 2/3: equality with hashed message in output@T *)
    (* honest case *)
    intro Ht Heq *.
    by exists j.

    (* case 3/3: equality with hashed message in update@T1 *)
    (* if there is an update@T1, then action T happened before *)
    intro Ht Heq *.
    use lastUpdateTag with pred(T1(ii,j)),ii,j as H2; 
      2,3: depends T(ii,j),T1(ii,j); by auto; intro Ht'; by auto.
    depends T(ii,j),T1(ii,j); 1: by auto.
    intro Ht'.
    by exists j.
Qed.

goal auth_T1_induction :
  forall (t:timestamp), forall (i,j:index),
    happens(t) =>
      ((t = T1(i,j) && exec@t) (* exec@t (not only cond@t) is needed *)
      =>
      (exists (jj:index), R1(jj,i) < t && output@R1(jj,i) = input@t)).
Proof.
  induction.
  intro t IH0 i j Hap [Ht Hexec].
  subst t,T1(i,j).
  expand exec@T1(i,j). expand cond@T1(i,j).
  destruct Hexec as [H1 Meq].
  euf Meq.

    (* case 1/2: equality with hashed message in output@R1 *)
    (* honest case *)
    intro Ht Heq *.
    by exists jj.

    (* case 2/2: equality with hashed message in update@T1 *)
    intro Ht Heq *.
    use IH0 with T1(i,j0),i,j0; 2,3: by auto.
    executable pred(T1(i,j)); 1,2: by auto.
    simpl_left.
    intro H.
    use H with T1(i,j0) as H'; 2: by auto.
    expand exec@T1(i,j0). expand cond@T1(i,j0).
    destruct H' as [H2 Meq'].
    by exists jj.
    split; 1: by auto.
    executable pred(T1(i,j)); 1,2: by auto.
    intro H.  by use H with T1(i,j0).
Qed.

(* Tentative without induction, seems not doable. *)
goal auth_R1 :
  forall (jj,ii:index), 
    happens(R1(jj,ii)) =>
      (cond@R1(jj,ii) 
      =>
      (exists (j:index), 
        T(ii,j) < R1(jj,ii) && output@T(ii,j) = input@R1(jj,ii))).
Proof.
  intro jj ii Hap Hcond.
  expand cond@R1(jj,ii).
  euf Hcond.

    (* case 1/3: equality with hashed message in update@R1 *)
    (* this case is easily handled in the version with induction
    (see auth_R1_induction) because the induction hypothesis
    allows to conclude using only the fact that R1(jj1,ii) < R1(jj,ii),
    we do not have to exploit the equality hypothesis generated by the
    euf tactic *)
    (* here, without the induction, we have to find another way to conclude *)
    intro Ht M1 *.
    assert
      input@R1(jj,ii) =
        h1(xor(xor(fst(kR(ii)@pred(R1(jj0,ii))),r1(jj0)),k(ii)),key1(ii))
      as Hcond'.
    by congruence.
    euf Hcond'. (* here again, we have 3 different cases *)

      (* case 1/3: equality with hashed message in update@R1 *)
      admit. (* ??? *)

      (* case 2/3: equality with hashed message in output@T *)
      (* honest case *)
      intro Ht' M2 *.
      exists j. split.
      case Ht'; 1,2: by eqtrace.
      case Ht'; 1,2: by expand output@T(ii,j); congruence.

      (* case 3/3: equality with hashed message in update@T1 *)
      (* if there is an update@T1, then action T happened before *)
      intro Ht' M2 *.
      use lastUpdateTag with pred(T1(ii,j)),ii,j as M3;
        2,3: by depends T(ii,j),T1(ii,j); case Ht'; 1,2: auto; intro Hdep; auto. 
      depends T(ii,j),T1(ii,j). case Ht'; 1,2: by auto.
      intro Hdep.
      exists j. split.
      case Ht'; 1,2: by eqtrace. 
      case Ht'; 1,2: by expand output@T(ii,j); congruence. 

    (* case 2/3: equality with hashed message in output@T *)
    (* honest case *)
    intro Ht M1 *.
    exists j. split; 1,2: by auto.

    (* case 3/3: equality with hashed message in update@T1 *)
    (* if there is an update@T1, then action T happened before *)
    intro Ht M1 *.
    use lastUpdateTag with pred(T1(ii,j)),ii,j as M2;
      2,3: by depends T(ii,j),T1(ii,j); auto.
    depends T(ii,j),T1(ii,j); 1: by auto.
    intro Hdep.
    exists j. split; 1,2: by auto.
Qed.