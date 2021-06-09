(*******************************************************************************
YUBIKEY

[1] R. Künnemann, "Foundations for analyzing security APIs in the symbolic and
computational model’, 2014.

C -> S : pid || otp || nonce
S -> C : otp || nonce || hmac || status

COMMENTS
- The last message is unclear and not modelled at all and replaced by "accept".
It was also not modelled in the Tamarin/Sapic file provided in Robert's thesis.
- otp is an encryption of a triple (secret(i), cpt, npr(i,j)).
It is modelled here as a randomized encryptio of a pair (secret(i), cpt).
According to the specification in Robert's thesis, AES is used.
The proof relies on intctxt... not sure that this is legitimate.

PROOFS 
- counterIncrease
- noreplay
- monotonicity
- authentication (non-injective and injective)
- lastUpdate (but not useful)

*******************************************************************************)

set autoIntro = false.

senc enc,dec

abstract startplug: message
abstract endplug: message
abstract startpress: message
abstract accept:message
abstract myzero: message
abstract myone: message

abstract mySucc : message->message

abstract pid : index -> message
name k: index -> message
name secret: index -> message
name nonce: index->index->message
name npr: index->index->message

mutable YCpt(i:index): message = myzero
mutable SCpt(i:index): message = myzero

channel cT
channel cR

abstract orderOk : message
abstract order : message->message->message

(* When the key is plugged, its counter is incremented *)
process yubikeyplug(i:index,j:index) =
  in(cT, x1);
  if x1 = startplug then YCpt(i) := succ(YCpt(i)); out(cT,endplug)

(* When the key is pressed, an otp is sent with the current value of the counter,
and the counter is imcremented *)
process yubikeypress(i:index,j:index) =
  in(cT,x2);
  if x2 = startpress then
    let cpt = YCpt(i) in
    YCpt(i) := mySucc(YCpt(i));
    out(cT,<pid(i),<nonce(i,j),enc(<secret(i),cpt>,npr(i,j),k(i))>>)

(* When the server receives a message, it checks whether it corresponds to a pid
in its database, and checks also that the counter inside the otp is strictly 
greater than the counter associated to the token. 
If so, the value inside the otp is used to update the database.
Now, the counter value associated to this token is this new value. *)
(* WARNING - If the non-failure test "dec(snd(snd(y1)),k(i)) <> fail" is
replaced by "fst(dec(snd(snd(y1)),k(i))) = secret(i)",
we are unable to use intctxt and prove the goal auth. *)
process server(ii:index) =
  in(cR,y1);
  try find i such that fst(y1) = pid(i) in
    if dec(snd(snd(y1)),k(i)) <> fail 
        && order(SCpt(i),snd(dec(snd(snd(y1)),k(i)))) = orderOk 
    then
      SCpt(i) := snd(dec(snd(snd(y1)),k(i)));
      out(cR,accept)

system 
  ( (!_i !_j Plug: yubikeyplug(i,j)) 
    | (!_i !_j Press: yubikeypress(i,j)) 
    | (!_ii S: server(ii))).

axiom orderTrans :
  forall (n1,n2,n3:message),
    (order(n1,n2) = orderOk && order(n2,n3) = orderOk)
      => order(n1,n3) = orderOk

axiom orderStrict : 
  forall (n1,n2:message), n1 = n2 => order(n1,n2) <> orderOk.
  
(* The counter SCpt(i) strictly increases when t is an action S performed by 
the server with tag i. *)
goal counterIncreaseStrictly:
  forall (ii,i:index), happens(S(ii,i)) =>
    (cond@S(ii,i) => order(SCpt(i)@pred(S(ii,i)),SCpt(i)@S(ii,i)) = orderOk).
Proof.
  intro ii i Hap Hcond.
  expand cond@S(ii,i).
  destruct Hcond as [Mneq Morder Meq].
  expand SCpt(i)@S(ii,i).
  by assumption.
Qed.

(* The counter SCpt(i) increases (not strictly) between pred(t) and t. *)
goal counterIncrease:
  forall (t:timestamp), happens(t) =>
    (forall (i:index),
      (t > init && exec@t) =>
        (order(SCpt(i)@pred(t),SCpt(i)@t) = orderOk 
        || SCpt(i)@t = SCpt(i)@pred(t))).
Proof.
  intro t Hap i [Ht Hexec].
  case t; 1,2,3,4,5,7,8: by auto.

  intro H. simpl_left.
  assert (i = i0 || i <> i0) as Hi. by auto.
  case Hi.
    (* i = i0 *)
    left.
    subst t, S(ii,i).
    expand exec@S(ii,i).
    by use counterIncreaseStrictly with ii, i.
    (* i <> i0 *)
    right.
    subst t, S(ii,i0).
    case 
      (if i = i0 then snd(dec(snd(snd(input@S(ii,i0))),k(i0))) 
       else SCpt(i)@pred(S(ii,i0))).
    by auto.
    expand SCpt(i)@S(ii,i0).
    intro [Hi' M].
    by assumption.
Qed.

(* The counter SCpt(i) increases (not strictly) between t' and t when t' < t *)
goal counterIncreaseBis:
  forall (t:timestamp), forall (t':timestamp), forall (i:index),
    happens(t) =>
      ((exec@t && t' < t) =>
        (order(SCpt(i)@t',SCpt(i)@t) = orderOk || SCpt(i)@t = SCpt(i)@t')).
Proof.
  induction.
  intro t IH0 t' i Hap [Hexec Ht'].
  assert (t' = pred(t) || t' < pred(t)) as H0; 1: by case t. 
  case H0.

  (* case t' = pred(t) *)
  use counterIncrease with t as H1; 2: by assumption.
  use H1 with i as H2; 2: by auto.
  subst pred(t), t'.
  by assumption.

  (* case t' < pred(t) *)
  use IH0 with pred(t),t',i as H1.
  use counterIncrease with t as H2; 2: by assumption.
  use H2 with i as H3.
  case H1.
    (* case H1 - 1/2 *)
    case H3.
      left.
      use orderTrans with SCpt(i)@t',SCpt(i)@pred(t),SCpt(i)@t.
      by congruence.
      split; 1,2: by assumption.
      by left; congruence.
      (* case H1 - 2/2 *)
      case H3.
      by left; congruence.
      by right; congruence.

      split; 1,2: by auto.
      by auto.
      by auto.
      executable t; 1,2: by assumption.
      intro H1.
      use H1 with pred(t) as H2.
      split; 1,2: by auto.
      by auto.
Qed.

goal noreplayInv:
  forall (ii, ii1, i:index), happens(S(ii1,i),S(ii,i)) =>
    (exec@S(ii1,i) && S(ii,i) < S(ii1,i)
      => order(SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i)) = orderOk).
Proof.
  intro ii ii1 i Hap [Hexec Ht].
  use counterIncreaseStrictly with ii1, i as M0.
  assert (S(ii,i) = pred(S(ii1,i)) || S(ii,i) < pred(S(ii1,i))) as H1.
  by constraints.
  case H1.

  (* case S(ii,i) = pred(S(ii1,i)) *)
  by congruence.

  (* case S(ii,i) < pred(S(ii1,i)) *)
  use counterIncreaseBis with pred(S(ii1,i)),S(ii,i),i as H2.
  case H2.
  use orderTrans with SCpt(i)@S(ii,i), SCpt(i)@pred(S(ii1,i)),SCpt(i)@S(ii1,i).
  by congruence.
  split; 1,2: by assumption.
  by congruence.
  by constraints.
  split.
  executable S(ii1,i); 1,2: by auto.
  intro H.
  use H with pred(S(ii1,i)) as Hexec'.
  by assumption.
  by constraints.
  by assumption.
  by constraints.
  expand exec@S(ii1,i).
  destruct Hexec as [Hpred Hcond].
  by assumption.
Qed.


goal noreplayNew:
  forall (ii, ii1, i:index), happens(S(ii1,i)) =>
    (exec@S(ii1,i) && S(ii,i) <= S(ii1,i) && SCpt(i)@S(ii,i) = SCpt(i)@S(ii1,i) 
     => ii = ii1).
Proof.
  intro ii ii1 i Hap [Hexec Ht Meq].
  assert (S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i)) as H1.
  by constraints.
  case H1.
  by constraints.
  use noreplayInv with ii, ii1, i as M1.
  use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i).
  by congruence.
  by assumption.
  split; 1,2: by constraints.
  split; 1,2: by assumption.
Qed.


goal monotonicity:
  forall (ii, ii1, i:index), happens(S(ii1,i),S(ii,i)) =>
    (exec@S(ii1,i) && exec@S(ii,i) && 
      order(SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i)) = orderOk
    => S(ii,i) < S(ii1,i)).
Proof.
  intro ii ii1 i Hap [Hexec H].
  assert
    (S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i) || S(ii,i) > S(ii1,i)) as Ht.
  by constraints.
  case Ht.
  (* case S(ii,i) = S(ii1,i) *)
  use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii,i); 1,2: by congruence.
  (* case S(ii,i) < S(ii1,i) *)
  by assumption.
  (* case S(ii,i) > S(ii1,i) *)
  use noreplayInv with ii1, ii, i as H'.
  use orderTrans with SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i), SCpt(i)@S(ii,i) as H''.
  use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii,i) as Mneq; 1,2: by congruence.
  split; 1,2: by assumption.
  split; 1,2: by constraints.
  split; 1,2: by auto.
Qed.

(* Non-injective version of authentication but, since the encryption outputted
by the yubikey contains a random number, this property should imply 
the injective one. *)
goal auth:
  forall (ii,i:index), happens(S(ii,i)) =>
    (cond@S(ii,i) =>
      (exists (j:index), 
        Press(i,j) < S(ii,i) 
        && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i))))).
Proof.
  intro ii i Hap Hcond.
  expand cond@S(ii,i).
  destruct Hcond as [Mneq Morder Meq].
  intctxt Mneq.

    intro Ht Meq' *.
    exists j. split.
    by eqtrace.
    expand output@Press(i,j). by congruence.

    intro Meq' *.
    by congruence.
Qed.

(* A first injective version for authentication. *)
(* WARNING - There is an admit which is true in the symbolic setting,
but we need an hypothesis in the computational model. *)
goal auth_injective_bis:
  forall (ii,i:index), happens(S(ii,i)) =>
    (cond@S(ii,i) =>
      (exists (j:index), 
      (Press(i,j) < S(ii,i) && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i)))) 
      && (forall (j':index), 
         (Press(i,j') < S(ii,i) 
         && snd(snd(output@Press(i,j'))) = snd(snd(input@S(ii,i)))) => j=j'))).
Proof.
  intro ii i Hap Hcond.
  expand cond@S(ii,i).
  destruct Hcond as [Mneq Morder Meq].
  intctxt Mneq.

  intro Ht Meq' *.
  exists j. split. split.
  by eqtrace.
  expand output@Press(i,j). by congruence.
  intro j' [Ht' Meq''].
  expand output@Press(i,j').
  assert
   (enc(<secret(i),cpt(i,j)@Press(i,j)>,npr(i,j),k(i)) = 
    enc(<secret(i),cpt(i,j')@Press(i,j')>,npr(i,j'),k(i))) 
   as H.
  by congruence.
  assert (npr(i,j) = npr(i,j')) as H1.
  admit.
  by eqnames.

  intro Meq' *.
  by congruence.
Qed.

(* Another injective version for authentication. *)
goal auth_injective:
   forall (ii,i:index), happens(S(ii,i)) =>
     (exec@S(ii,i) =>
       (exists (j:index),
       Press(i,j) < S(ii,i)
       && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i)))
       && (forall (ii1:index), happens(S(ii1,i)) =>
            ( (exec@S(ii1,i)
              && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii1,i)))
              && SCpt(i)@S(ii,i) = SCpt(i)@S(ii1,i))
              => ii1 = ii )))).
Proof.
  intro ii i Hap Hexec.
  expand exec@S(ii,i).
  expand cond@S(ii,i).
  destruct Hexec as [Hpred [Mneq M1 M2]].
  intctxt Mneq; 2: intro *; by congruence.
  intro Ht M3 *.
  exists j.
  split. split.
  by assumption.
  by expand output@Press(i,j); congruence.
  intro ii1 Hap' [Hexec' M4 M5].
  expand exec@S(ii1,i).
  expand cond@S(ii1,i).
  expand output@Press(i,j).
  destruct Hexec' as [Hpred' [Mneq' M6 M7]].
  assert
   ( S(ii,i) < S(ii1,i) || S(ii,i) = S(ii1,i) || S(ii,i) > S(ii1,i) ) as H.
  by constraints.
  case H.

  (* case S(ii,i) < S(ii1,i) *)
  assert
   order(SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i)) = orderOk as M8.
  assert
   ( S(ii,i) < pred(S(ii1,i)) || S(ii,i) = pred(S(ii1,i)) || S(ii,i) > pred(S(ii1,i)) ) as H'.
  by constraints.
  case H'.
  (* case S(ii,i) < pred(S(ii1,i)) *)
  use counterIncreaseBis with pred(S(ii1,i)),S(ii,i),i as Hcpt.
  case Hcpt.
  use orderTrans with SCpt(i)@S(ii,i),SCpt(i)@pred(S(ii1,i)),SCpt(i)@S(ii1,i) as M8.
  by assumption.
  split.
  by assumption.
  expand SCpt(i)@S(ii1,i); by congruence.
  expand SCpt(i)@S(ii1,i); by congruence.
  by constraints.
  split; 1,2: by assumption.
  (* S(ii,i) = pred(S(ii1,i)) *)
  by expand SCpt(i)@S(ii1,i); congruence.
  (* S(ii,i) > pred(S(ii1,i)) *)
  by constraints.

  use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i) as M8'.
  by congruence.
  by assumption.

  (* case S(ii,i) = S(ii1,i) *)
  by constraints.

  (* case S(ii,i) > S(ii1,i) *)
  assert
   order(SCpt(i)@S(ii1,i),SCpt(i)@S(ii,i)) = orderOk as M8.
  assert
   ( S(ii1,i) < pred(S(ii,i)) || S(ii1,i) = pred(S(ii,i)) || S(ii1,i) > pred(S(ii,i)) ) as H'.
  by constraints.
  case H'.
  (* case S(ii1,i) < pred(S(ii,i)) *)
  use counterIncreaseBis with pred(S(ii,i)),S(ii1,i),i as Hcpt.
  case Hcpt.
  use orderTrans with SCpt(i)@S(ii1,i),SCpt(i)@pred(S(ii,i)),SCpt(i)@S(ii,i) as M8.
  by assumption.
  split.
  by assumption.
  expand SCpt(i)@S(ii,i); by congruence.
  expand SCpt(i)@S(ii,i); by congruence.
  by constraints.
  split; 1,2: by assumption.
  (* S(ii1,i) = pred(S(ii,i)) *)
  by expand SCpt(i)@S(ii,i); by congruence.
  (* S(ii1,i) > pred(S(ii,i)) *)
  by constraints.

  use orderStrict with SCpt(i)@S(ii1,i),SCpt(i)@S(ii,i) as M8'.
  by congruence.
  by congruence.
Qed.

(******************************************************************************)

(* This lemma is not useful for the previous proofs. *)
goal lastUpdateServer_:
  forall (t:timestamp), forall (i:index), happens(t) =>
    ((SCpt(i)@t = SCpt(i)@init 
      && forall (ii:index), happens(S(ii,i)) => t<S(ii,i))
    ||
    (exists ii:index, SCpt(i)@t = SCpt(i)@S(ii,i) && S(ii,i) <= t &&
      (forall (ii':index), 
        happens(S(ii',i)) => (S(ii',i) <= S(ii,i) || t < S(ii',i))))).
Proof.
  induction. intro t IH0.
  intro i Hap.
  case t.

  (* 1/8 *)
  intro _; simpl_left; subst t, init.
  by left.

  (* 2/8 *)
  intro _; simpl_left; subst t, Plug(i0,j).
  use IH0 with pred(Plug(i0,j)),i as H1; 2,3: by auto.
  expand SCpt(i)@Plug(i0,j).
  case H1.
  destruct H1 as [H2 H3].
  left. split.
  by assumption.  
  intro ii Hap'.
  use H3 with ii; 1,2: by auto.
  right. simpl_left.
  exists ii.
  split. split.
  by assumption.
  by constraints.
  intro jj' Hap'.
  use H0 with jj' as H1; 2: by assumption.
  case H1.
  left; by assumption.
  right; by constraints.

  (* 3/8 *)
  intro _; simpl_left; subst t, Plug1(i0,j).
  use IH0 with pred(Plug1(i0,j)),i as H1; 2,3: by auto.
  expand SCpt(i)@Plug1(i0,j).
  case H1.
  destruct H1 as [H2 H3].
  left. split.
  by assumption.  
  intro ii Hap'.
  use H3 with ii; 1,2: by auto.
  right. simpl_left.
  exists ii.
  split. split.
  by assumption.
  by constraints.
  intro jj' Hap'.
  use H0 with jj' as H1; 2: by assumption.
  case H1.
  left; by assumption.
  right; by constraints.

  (* 4/8 *)
  intro _; simpl_left; subst t, Press(i0,j).
  use IH0 with pred(Press(i0,j)),i as H1; 2,3: by auto.
  expand SCpt(i)@Press(i0,j).
  case H1.
  destruct H1 as [H2 H3].
  left. split.
  by assumption.  
  intro ii Hap'.
  use H3 with ii; 1,2: by auto.
  right. simpl_left.
  exists ii.
  split. split.
  by assumption.
  by constraints.
  intro jj' Hap'.
  use H0 with jj' as H1; 2: by assumption.
  case H1.
  left; by assumption.
  right; by constraints.

  (* 5/8 *)
  intro _; simpl_left; subst t, Press1(i0,j).
  use IH0 with pred(Press1(i0,j)),i as H1; 2,3: by auto.
  expand SCpt(i)@Press1(i0,j).
  case H1.
  destruct H1 as [H2 H3].
  left. split.
  by assumption.  
  intro ii Hap'.
  use H3 with ii; 1,2: by auto.
  right. simpl_left.
  exists ii.
  split. split.
  by assumption.
  by constraints.
  intro jj' Hap'.
  use H0 with jj' as H1; 2: by assumption.
  case H1.
  left; by assumption.
  right; by constraints.

  (* 6/8 - interesting case *)
  intro _; simpl_left; subst t, S(ii,i0).
  use IH0 with pred(S(ii,i0)),i as H1; 2,3: by auto.
  case H1.

    (**)
    destruct H1 as [H2 H3].
    assert (i=i0 || i<>i0) as H4. by auto.
    case H4.
    (* i = i0 *)
    right.
    exists ii.
    split. by auto.
    intro ii' Hap'.
    use H3 with ii'; 2: by assumption.
    by auto.
    (* i <> i0 *)
    left.
    split.
    expand SCpt(i)@S(ii,i0).
    case (if i=i0 then snd(dec(snd(snd(input@S(ii,i0))),k(i0))) else
    SCpt(i)@pred(S(ii,i0))).
    intro Hif.
    destruct Hif as [Hif1 Hif2].  
    by constraints.
    intro Hif.
    destruct Hif as [Hif1 Hif2].  
    by assumption.
    intro ii0 Hap0.
    use H3 with ii0; 1,2: by auto.

    (**)
    simpl_left.
    assert (i=i0 || i<>i0) as H2. by auto.
    case H2.
    assert (ii=ii0 || ii<>ii0) as H3. by auto.
    case H3.
    (* i = i0 && ii = i0 *)
    by constraints.
    (* i = i0 && ii <> i0 *)
    right.
    exists ii.
    split. by auto.
    intro ii' Hap'.
    by auto.
    (* i <> i0 *)
    right.
    exists ii0.
    split. split.
    expand SCpt(i)@S(ii,i0).
    case (if i = i0 then snd(dec(snd(snd(input@S(ii,i0))),k(i0))) else
    SCpt(i)@pred(S(ii,i0))).
    intro Hif.
    destruct Hif as [Hif1 Hif2].
    by constraints.
    intro Hif.
    destruct Hif as [Hif1 Hif2].
    by assumption.
    by constraints.
    intro ii' Hap'.
    use H0 with ii' as Ht; 2: by assumption.
    case Ht.
    by left; constraints.
    assert (ii=ii' || ii<>ii') as C'.
    by constraints.
    case C'.
    by right; constraints.
    by right; constraints.

  (* 7/8 *)
  intro _; simpl_left; subst t, S1(ii,i0).
  use IH0 with pred(S1(ii,i0)),i as H1; 2,3: by auto.
  expand SCpt(i)@S1(ii,i0).
  case H1.
  destruct H1 as [H2 H3].
  left. split.
  by assumption.  
  intro ii0 Hap'.
  use H3 with ii0; 1,2: by auto.
  right. simpl_left.
  exists ii0.
  split. split.
  by assumption.
  by constraints.
  intro jj' Hap'.
  use H0 with jj' as H1; 2: by assumption.
  case H1.
  left; by assumption.
  right; by constraints.

  (* 8/8 *)
  intro _; simpl_left; subst t, S2(ii).
  use IH0 with pred(S2(ii)),i as H1; 2,3: by auto.
  expand SCpt(i)@S2(ii).
  case H1.
  destruct H1 as [H2 H3].
  left. split.
  by assumption.  
  intro ii0 Hap'.
  use H3 with ii0; 1,2: by auto.
  right. simpl_left.
  exists ii0.
  split. split.
  by assumption.
  by constraints.
  intro jj' Hap'.
  use H0 with jj' as H1; 2: by assumption.
  case H1.
  left; by assumption.
  right; by constraints.
Qed.
