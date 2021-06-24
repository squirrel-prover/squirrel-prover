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
It is modelled here as a randomized encryption of a pair (secret(i), cpt).
According to the specification in Robert's thesis, AES is used.
WARNING The proof relies on intctxt... not sure that this is legitimate.

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
abstract (~<) : message->message->message

(* When the key is plugged, its counter is incremented *)
process yubikeyplug(i:index,j:index) =
  in(cT, x1);
  if x1 = startplug then YCpt(i) := mySucc(YCpt(i)); out(cT,endplug)

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
we are unable to use intctxt and thus to prove the goal auth. *)
process server(ii:index) =
  in(cR,y1);
  try find i such that fst(y1) = pid(i) in
    if dec(snd(snd(y1)),k(i)) <> fail 
        && SCpt(i) ~< snd(dec(snd(snd(y1)),k(i))) = orderOk 
    then
      SCpt(i) := snd(dec(snd(snd(y1)),k(i)));
      out(cR,accept).

system 
  ( (!_i !_j Plug: yubikeyplug(i,j)) 
    | (!_i !_j Press: yubikeypress(i,j)) 
    | (!_ii S: server(ii))).


(* LIBRARIES *)
(* A inclure dans une lib standard *)

goal eq_sym ['a] (x,y : 'a) : x = y => y = x.
Proof. auto. Qed.

goal if_false ['a] (b : boolean, x,y : 'a):
 (not b) => if b then x else y = y.
Proof.
 by intro *; noif. 
Qed.

goal if_true ['a] (b : boolean, x,y : 'a):
 b => if b then x else y = x.
Proof.
  by intro *; yesif.
Qed.

goal if_true0 ['a] (x,y : 'a):
 if true then x else y = x.
Proof.
  by rewrite if_true. 
Qed.
hint rewrite if_true0.

goal if_false0 ['a] (x,y : 'a):
 if false then x else y = y.
Proof.
  by rewrite if_false.
Qed.
hint rewrite if_false0.

goal fst_pair (x,y : message) : fst (<x,y>) = x.
Proof. auto. Qed.
hint rewrite fst_pair.

goal snd_pair (x,y : message) : snd (<x,y>) = y.
Proof. auto. Qed.
hint rewrite snd_pair.

goal dec_enc (x,y,z:message) : dec(enc(x,z,y),y) = x.
Proof. auto. Qed.
hint rewrite dec_enc.


(* PROOF *)

axiom orderTrans (n1,n2,n3:message):
  n1 ~< n2 = orderOk && n2 ~< n3 = orderOk => n1 ~< n3 = orderOk.

axiom orderStrict (n1,n2:message):
   n1 = n2 => n1 ~< n2 <> orderOk.
  
axiom orderSucc (n1:message):
n1 ~< mySucc(n1) = orderOk.

(* The counter SCpt(i) strictly increases when t is an action S performed by 
the server with tag i. *)
goal counterIncreaseStrictly (ii,i:index):
   happens(S(ii,i)) =>
   cond@S(ii,i) => 
   SCpt(i)@pred(S(ii,i)) ~< SCpt(i)@S(ii,i) = orderOk.
Proof. auto. Qed.

(* The counter SCpt(i) increases (not strictly) between pred(t) and t. *)
goal counterIncrease (t:timestamp, i : index) :
  happens(t) =>
  t > init && exec@t =>
    SCpt(i)@pred(t) ~< SCpt(i)@t = orderOk ||
    SCpt(i)@t = SCpt(i)@pred(t).
Proof.
  intro Hap [Ht Hexec].
  case t => //.

  intro [ii i0 _].
  case (i = i0) => _.
    (* i = i0 *)
    by left.
    (* i <> i0 *)
    right. 
    by rewrite /SCpt if_false.
Qed.

(* The counter SCpt(i) increases (not strictly) between t' and t when t' < t *)
goal counterIncreaseBis:
  forall (t:timestamp), forall (t':timestamp), forall (i:index),
    happens(t) =>
    exec@t && t' < t =>
    ( SCpt(i)@t' ~< SCpt(i)@t = orderOk || 
      SCpt(i)@t = SCpt(i)@t').
Proof.
  induction.
  intro t IH0 t' i Hap [Hexec Ht'].
  assert (t' = pred(t) || t' < pred(t)) as H0; 
  1: case t; constraints. 
  case H0.

  (* case t' = pred(t) *)
  rewrite !H0. 

  by apply counterIncrease.

  (* case t' < pred(t) *)
  use IH0 with pred(t),t',i as H1 => //.
  use counterIncrease with t,i as H3 => //.
  case H1 => //.
    (* case H1 - 1/2 *)
    case H3 => //.
      by left; apply orderTrans _ (SCpt(i)@pred(t)) _.
      (* case H1 - 2/2 *)
      by case H3; [1: left | 2 : right].
  
      simpl.
      executable t => // H1. 
      by apply H1.
Qed.


(* Counters on the Yubikey side *)

goal YPresscounterIncreaseStrictly (i,j:index):
   happens(Press(i,j)) =>
   cond@Press(i,j) => 
   YCpt(i)@pred(Press(i,j)) ~< YCpt(i)@Press(i,j) = orderOk.
Proof.
intro Hap Hcond.
expand YCpt(i)@Press(i,j).
apply orderSucc.
Qed.

goal YPlugcounterIncreaseStrictly (i,j:index):
   happens(Plug(i,j)) =>
   cond@Plug(i,j) => 
   YCpt(i)@pred(Plug(i,j)) ~< YCpt(i)@Plug(i,j) = orderOk.
Proof.
intro Hap Hcond.
expand YCpt(i)@Plug(i,j).
apply orderSucc.
Qed.

goal YcounterIncrease (t:timestamp, i : index) :
  happens(t) =>
  t > init && exec@t =>
    YCpt(i)@pred(t) ~< YCpt(i)@t = orderOk ||
    YCpt(i)@t = YCpt(i)@pred(t).
Proof.
  intro Hap [Ht Hexec].
  case t => //.

   (* Plug *)
  intro [i0 j _].
  case (i = i0) => _.
    (* i = i0 *)
   left.
   use YPlugcounterIncreaseStrictly with i, j as H1 => //.
    (* i <> i0 *)
    right. 
    by rewrite /YCpt if_false.

   (* Press *)
   intro [i0 j _].
   case (i = i0) => _.
    (* i = i0 *)
   left.
   use YPresscounterIncreaseStrictly with i, j as H1 => //.
    (* i <> i0 *)
    right. 
    by rewrite /YCpt if_false.

Qed.



goal YcounterIncreaseBis:
  forall (t:timestamp), forall (t':timestamp), forall (i:index),
    happens(t) =>
    exec@t && t' < t =>
    ( YCpt(i)@t' ~< YCpt(i)@t = orderOk || 
      YCpt(i)@t = YCpt(i)@t').
Proof.
  induction.
  intro t IH0 t' i Hap [Hexec Ht'].
  assert (t' = pred(t) || t' < pred(t)) as H0; 
  1: case t; constraints. 
  case H0.

  (* case t' = pred(t) *)
  rewrite !H0. 

  by apply YcounterIncrease.

  (* case t' < pred(t) *)
  use IH0 with pred(t),t',i as H1 => //.

  use YcounterIncrease with t,i as H3 => //.
  case H1 => //.
    (* case H1 - 1/2 *)
    case H3 => //.
      by left; apply orderTrans _ (YCpt(i)@pred(t)) _.
      (* case H1 - 2/2 *)
      by case H3; [1: left | 2 : right].
  
      simpl.
      executable t => //.
      intro H1.
      by apply H1.
Qed.

(* Authentication following a suggestion of Adrien *)

goal auth_injective_ter (ii,i:index):
  happens(S(ii,i)) =>
  exec@S(ii,i) =>
    exists (j:index), 
     (Press(i,j) < S(ii,i) && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i))))
     && forall (j':index), 
       (Press(i,j') < S(ii,i) && 
       snd(snd(output@Press(i,j'))) = snd(snd(input@S(ii,i)))) => 
         j=j'.
Proof.
intro Hap Hexec.
executable S(ii,i) => //.
intro exec.
expand exec, cond.
destruct Hexec as [Hexecpred [Mneq Hcpt Hpid]].
intctxt Mneq => //.
intro Ht M1 *.
exists j.
split => //.
intro j'.
intro [Hyp Meq].
expand output@Press(i,j').
rewrite snd_pair in Meq.
rewrite snd_pair in Meq.


expand cpt.
assert(snd(dec(enc(<secret(i),YCpt(i)@pred(Press(i,j))>,npr(i,j),k(i)),k(i))) = snd(dec(enc(<secret(i),YCpt(i)@pred(Press(i,j'))>,npr(i,j),k(i)),k(i)))) => //.
rewrite dec_enc in Meq0.
rewrite dec_enc in Meq0.
rewrite snd_pair in Meq0.
rewrite snd_pair in Meq0.

assert(YCpt(i)@Press(i,j) = YCpt(i)@Press(i,j')).
expand YCpt => //.


assert
   ( Press(i,j) = Press(i,j') || Press(i,j) < Press(i,j') || Press(i,j) > Press(i,j') ) as H => //.
case H => //.



(* Press(i,j) < Press(i,j') *)
use exec with Press(i,j') as H0' => //.
expand exec.
use YPresscounterIncreaseStrictly with i, j' as HP' => //.

assert(pred(Press(i,j')) = Press(i,j) || pred(Press(i,j')) > Press(i,j)) => //.
case H0.
 
 (* pred(Press(i,j')) = Press(i,j)  *)
 use orderStrict with YCpt(i)@Press(i,j), YCpt(i)@Press(i,j') => //.
 (* pred(Press(i,j')) > Press(i,j) *)
use YcounterIncreaseBis with pred(Press(i,j')), Press(i,j), i as HI => //.
case HI => //.
use orderTrans with  YCpt(i)@Press(i,j), YCpt(i)@pred(Press(i,j')), YCpt(i)@Press(i,j') => //.
use orderStrict with YCpt(i)@Press(i,j), YCpt(i)@Press(i,j') => //.
rewrite HI in Meq0 =>//.
expand YCpt(i)@Press(i,j).
use orderSucc with YCpt(i)@pred(Press(i,j)) => //.
use orderStrict with YCpt(i)@pred(Press(i,j)), mySucc(YCpt(i)@pred(Press(i,j))) => //.


(* Press(i,j) > Press(i,j') *)
use exec with Press(i,j) as H0 => //.
expand exec.
use YPresscounterIncreaseStrictly with i, j as HP => //.

assert(pred(Press(i,j)) = Press(i,j') || pred(Press(i,j)) > Press(i,j')) => //.
case H1.

 (* pred(Press(i,j)) = Press(i,j')  *)
 use orderStrict with YCpt(i)@Press(i,j'), YCpt(i)@Press(i,j) => //.
 (* pred(Press(i,j)) > Press(i,j') *)
use YcounterIncreaseBis with pred(Press(i,j)), Press(i,j'), i as HI => //.
case HI => //.
use orderTrans with  YCpt(i)@Press(i,j'), YCpt(i)@pred(Press(i,j)), YCpt(i)@Press(i,j) => //.
use orderStrict with YCpt(i)@Press(i,j'), YCpt(i)@Press(i,j) => //.
rewrite HI in Meq0 =>//.
expand YCpt(i)@Press(i,j').
use orderSucc with YCpt(i)@pred(Press(i,j')) => //.
use orderStrict with YCpt(i)@pred(Press(i,j')), mySucc(YCpt(i)@pred(Press(i,j'))) => //.
Qed.




(* Some security properties *)


goal noreplayInv (ii, ii1, i:index):
   happens(S(ii1,i),S(ii,i)) =>
   exec@S(ii1,i) && S(ii,i) < S(ii1,i) => 
   SCpt(i)@S(ii,i) ~< SCpt(i)@S(ii1,i) = orderOk.
Proof.
  intro Hap [Hexec Ht].
  use counterIncreaseStrictly with ii1, i as M0 => //.
  assert (S(ii,i) = pred(S(ii1,i)) || S(ii,i) < pred(S(ii1,i))) as H1; 
  1: constraints.
  case H1.

  (* case S(ii,i) = pred(S(ii1,i)) *)
  congruence.

  (* case S(ii,i) < pred(S(ii1,i)) *)
  use counterIncreaseBis with pred(S(ii1,i)),S(ii,i),i as H2 => //.
  case H2 => //; 1: by apply orderTrans _ (SCpt(i)@pred(S(ii1,i))) _.

  simpl.
  executable S(ii1,i) => // H.
  by apply H.
Qed.


goal noreplay (ii, ii1, i:index):
  happens(S(ii1,i)) =>
  exec@S(ii1,i) && S(ii,i) <= S(ii1,i) && SCpt(i)@S(ii,i) = SCpt(i)@S(ii1,i) => 
  ii = ii1.
Proof.
  intro Hap [Hexec Ht Meq].
  assert (S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i)) as H1; 1: constraints.
  case H1 => //.

  use noreplayInv with ii, ii1, i as M1 => //. 
  by apply orderStrict in Meq.
Qed.


goal monotonicity (ii, ii1, i:index):
  happens(S(ii1,i),S(ii,i)) =>
  exec@S(ii1,i) && exec@S(ii,i) && 
  SCpt(i)@S(ii,i) ~< SCpt(i)@S(ii1,i) = orderOk => 
  S(ii,i) < S(ii1,i).
Proof.
  intro Hap [Hexec H].
  assert
    (S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i) || S(ii,i) > S(ii1,i)) as Ht;
  1: constraints.
  case Ht.

  (* case S(ii,i) = S(ii1,i) *)
  by use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii,i).

  (* case S(ii,i) < S(ii1,i) *)
  assumption.

  (* case S(ii,i) > S(ii1,i) *)
  use noreplayInv with ii1, ii, i as Meq => //.
  (* apply orderTrans _ (SCpt(i)@S(ii1,i)) in H => //. *)
  use orderTrans with SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i), SCpt(i)@S(ii,i) => //.
  by use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii,i).
Qed.

(* Non-injective version of authentication but, since the encryption outputted
by the yubikey contains a random number, this property should imply 
the injective one. *)
goal auth (ii,i:index):
  happens(S(ii,i)) =>
  cond@S(ii,i) =>
  exists (j:index), 
    Press(i,j) < S(ii,i) 
    && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i))).
Proof.
  intro Hap Hcond.
  expand cond.
  destruct Hcond as [Mneq Morder Meq].
  intctxt Mneq => *; 1: by exists j.
  auto.
Qed.

(* A first injective version for authentication. *)
(* WARNING - There is an admit which is true in the symbolic setting,
but we need an hypothesis in the computational model. *)
goal auth_injective_bis (ii,i:index):
  happens(S(ii,i)) =>
  cond@S(ii,i) =>
    exists (j:index), 
     (Press(i,j) < S(ii,i) && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i))))
     && forall (j':index), 
       (Press(i,j') < S(ii,i) && 
       snd(snd(output@Press(i,j'))) = snd(snd(input@S(ii,i)))) => 
         j=j'.
Proof.
  intro Hap Hcond.
  expand cond.
  destruct Hcond as [Mneq Morder Meq].
  intctxt Mneq => // Ht Meq' *.

  exists j. 
  simpl. 
  split; 1: auto.
  intro j' [Ht' Meq''].
  expand output => /=.
  rewrite -Meq' in Meq''.
  assert (npr(i,j) = npr(i,j')) as H1. 
  admit.
  by eqnames.
Qed.

(* Another injective version for authentication. *)
goal auth_injective (ii,i:index):
   happens(S(ii,i)) =>
   exec@S(ii,i) =>
     exists (j:index),
       Press(i,j) < S(ii,i) && 
       snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i))) && 
       forall (ii1:index), happens(S(ii1,i)) =>
            exec@S(ii1,i) =>
            snd(snd(output@Press(i,j))) = snd(snd(input@S(ii1,i))) =>
            SCpt(i)@S(ii,i) = SCpt(i)@S(ii1,i) => 
            ii1 = ii.
Proof.
  intro Hap Hexec.
  expand exec, cond.
  destruct Hexec as [Hpred [Mneq M1 M2]].
  intctxt Mneq; 2: intro *; congruence.
  intro Ht M3 *.
  exists j.
  split; 1: auto. 
  intro ii1 Hap' Hexec' M4 M5.
  expand exec, cond, output.
  destruct Hexec' as [Hpred' [Mneq' M6 M7]].
  assert
   ( S(ii,i) < S(ii1,i) || S(ii,i) = S(ii1,i) || S(ii,i) > S(ii1,i) ) as H;
  1: constraints.
  case H; 2: auto.

  (* A: case S(ii,i) < S(ii1,i) *)
  assert SCpt(i)@S(ii,i) ~< SCpt(i)@S(ii1,i) = orderOk as M8.
  assert
   ( S(ii,i) < pred(S(ii1,i)) || 
     S(ii,i) = pred(S(ii1,i)) || 
     S(ii,i) > pred(S(ii1,i)) ) as H'; 1: constraints.

  case H'; 2,3: auto. 
  (* case S(ii,i) < pred(S(ii1,i)) *)
  use counterIncreaseBis with pred(S(ii1,i)),S(ii,i),i as Hcpt => //.
  case Hcpt => //.
  by apply orderTrans _ (SCpt(i)@pred(S(ii1,i))).

  (* S(ii,i) = pred(S(ii1,i)) *)
  by apply orderStrict in M5. 


  (* B: case S(ii,i) > S(ii1,i) *)
  assert SCpt(i)@S(ii1,i) ~< SCpt(i)@S(ii,i) = orderOk as M8.
  assert
   ( S(ii1,i) < pred(S(ii,i)) || 
     S(ii1,i) = pred(S(ii,i)) || 
     S(ii1,i) > pred(S(ii,i)) ) as H'; 1: constraints.
  case H'; 2,3: auto. 
  (* case S(ii1,i) < pred(S(ii,i)) *)
  use counterIncreaseBis with pred(S(ii,i)),S(ii1,i),i as Hcpt => //.
  case Hcpt; 
  [ 1: by apply orderTrans _ (SCpt(i)@pred(S(ii,i))) |
    2: auto].

  by apply orderStrict in M5. 
Qed.

(******************************************************************************)

(* This lemma is not useful for the previous proofs. *)
goal lastUpdateServer_ (t:timestamp, i:index):
  happens(t) =>
  (SCpt(i)@t = SCpt(i)@init && 
   forall (ii:index), happens(S(ii,i)) => t<S(ii,i))
   ||
   exists (ii:index), 
     SCpt(i)@t = SCpt(i)@S(ii,i) && S(ii,i) <= t &&
     forall (ii':index), 
        happens(S(ii',i)) => S(ii',i) <= S(ii,i) || t < S(ii',i).
Proof.
  generalize t i.
  induction => t IH0 i Hap.
  case t;
  try (
    intro Eq; repeat destruct Eq as [_ Eq];
    use IH0 with pred(t),i as H1 => //;
    clear IH0;
    expand SCpt;
    destruct H1 as [[_ H3] | [mi [_ _ H1]]];
    [ 1: left => /= mi *;
         by use H3 with mi |
      2: right;
         exists mi => /= jj' Hap';
         use H1 with jj' as H2 => //;
         by case H2; [ 1: left | 2 : right]]).

  (* init *)
  by intro *; left.

  (* interesting case *)
  intro [ii i0 _].
  use IH0 with pred(t),i as H1; 2,3: auto.
  case H1.

    (**)
    destruct H1 as [H2 H3].
    case (i=i0) => H4.
    (* i = i0 *)
    right.
    exists ii => /= ii' _. 
    by use H3 with ii'.

    (* i <> i0 *)
    left. 
    expand SCpt.
    rewrite if_false => // /=.
    intro ii0 _.
    by use H3 with ii0.

    (**)
    simpl_left.
    case (i=i0) => H2.
    case (ii=ii0) => H3.

    (* i = i0 && ii = i0 *)
    constraints.
    (* i = i0 && ii <> i0 *)
    right.
    exists ii. 
    simpl.
    auto.

    (* i <> i0 *)
    right.
    exists ii0. 
    simpl.
    split; 1: by rewrite /SCpt if_false.
    intro ii' _.
    use H0 with ii' as Ht; 2: assumption.
    by case Ht.
Qed.
