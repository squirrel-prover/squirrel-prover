(*******************************************************************************
YUBIKEY

C -> S: pid || otp || nonce
S -> C: otp || nonce || hmac || status

Warning: this last message is unclear and not modelled at all and replaced by "accept"
It was also not modelled in the Tamarin/Sapic file provided in Robert's thesis

otp is an encryption of a triple (secret(i), cpt, npr(i,j)), and it is modelled here as a randomized encryptio of a pair (secret(i), cpt).
According to the specification in Robert's thesis, AES is used.
I rely on intctxt ... not sure that this is legitimate.
*******************************************************************************)
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

(* When the server receives a message, it checks whether it corresponds to a pid in its database,
and checks also that the counter inside the otp is strictly greater than the counter associated to
the token. If so, the value inside the otp is used to update the database.
Now, the counter value associated to this token is this new value *)

(* Warning: If I replace the non-failure test "dec(snd(snd(y1)),k(i)) <> fail"
by fst(dec(snd(snd(y1)),k(i))) = secret(i)"  I an unable to use intctxt and with prove the goal auth *)
process server(ii:index) =
  in(cR,y1);
   try find  i such that fst(y1) = pid(i) in
     if  dec(snd(snd(y1)),k(i)) <> fail && order(SCpt(i),snd(dec(snd(snd(y1)),k(i)))) =orderOk then
     SCpt(i) := snd(dec(snd(snd(y1)),k(i)));
     out(cR,accept)


system ((!_i !_j Plug: yubikeyplug(i,j)) | (!_i !_j Press: yubikeypress(i,j)) | (!_ii S: server(ii))).

axiom orderTrans :
  forall (n1,n2,n3:message),
    (order(n1,n2) = orderOk && order(n2,n3) = orderOk)
    => order(n1,n3) = orderOk

axiom orderStrict : forall (n1,n2:message), n1 = n2 => order(n1,n2) <> orderOk.


(* I expressed a non-injective version of authentication but since the encryption outputted by the yubikey contains a random number, I think that this property will imply the injective one *)
(* This is one of the property stated by Robert *)
goal auth:
  forall (ii,i:index), happens(S(ii,i)) =>
    (cond@S(ii,i) =>
      (exists (j:index), 
      Press(i,j) < S(ii,i) 
      && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i))))).
Proof.
intro ii i Hap Hcond.
expand cond@S(ii,i).
intctxt Mneq.
by exists j.
Qed.

(* injectivity version Stephanie *)
(* Warning: admit which is true in the symbolic setting but we need an hypothesis in the computational model *)
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
intctxt Mneq.
exists j.
expand output@Press(i,j').
assert
 (enc(<secret(i),cpt(i,j)@Press(i,j)>,npr(i,j),k(i)) = enc(<secret(i),cpt(i,j')@Press(i,j')>,npr(i,j'),k(i)))  as H.
assert
 (npr(i,j) = npr(i,j')) as H1.
help.
admit.
Qed.



(* The counter SCpt(i) strictly increases when t is an action S performed by the the server with tag i. *)
goal counterIncreaseStrictly:
  forall (ii,i:index), happens(S(ii,i)) =>
    (cond@S(ii,i) => order(SCpt(i)@pred(S(ii,i)),SCpt(i)@S(ii,i)) = orderOk).
Proof.
intro ii i Hap Hcond.
by expand cond@S(ii,i).
Qed.


(* The counter SCpt(i) increases (not strictly) between pred(t) and t *)
goal counterIncrease:
  forall (t:timestamp), happens(t) =>
    (forall (i:index),
      (t > init && exec@t) =>
        (order(SCpt(i)@pred(t),SCpt(i)@t) = orderOk 
        || SCpt(i)@pred(t) = SCpt(i)@t)).
Proof.
intro *.
case t;
1,2,3,4,6,7: by right.

assert (i = i1 || i <> i1) as H1.
case H1.
(* i = i1 *)
left.
subst t, S(ii,i).
expand exec@S(ii,i).
by use counterIncreaseStrictly with ii, i.
(* i <> i1 *)
right.
by case(if i = i1 then snd(dec(snd(snd(input@S(ii,i1))),k(i1))) else
       SCpt(i)@pred(S(ii,i1))).
Qed.



(* The counter SCpt(i) increases (not strictly) between t' and t when t' < t *)
goal counterIncreaseBis:
  forall (t:timestamp), forall (t':timestamp), forall (i:index),
    happens(t) =>
      ((exec@t && t' < t) =>
        (order(SCpt(i)@t',SCpt(i)@t) = orderOk || SCpt(i)@t' = SCpt(i)@t)).
Proof.
nosimpl(induction; intro IH0).
intro t' i *.
assert (t' = pred(t) || t' <pred(t)) as H0; 1: by case t. 
case H0.

(* case t' = pred(t) *)
use counterIncrease with t as H1. use H1 with i as H2.
by subst pred(t), t'.

(* case t' < pred(t) *)
use IH0 with pred(t),t',i as H0.
executable t.
use H1 with pred(t) as H2.
use counterIncrease with t as H3. use H3 with i as H4. 
case H0. case H4.
(* 1/2 *)
left.
by use orderTrans with SCpt(i)@t',SCpt(i)@pred(t),SCpt(i)@t.
(* 2/2 *)
by case H4.

executable t.
by use H0 with pred(t) as H1.
Qed.

(* Solene: This is an injective version of the authentication property shown before.*)
goal auth_injective:
   forall (ii,i:index), happens(S(ii,i)) =>
     (exec@S(ii,i) =>
       (exists (j:index),
       Press(i,j) < S(ii,i)
       && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i)))
       && (forall (ii1:index), happens(S(ii1,i)) =>
            ( (exec@S(ii1,i)
              && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii1,i)))
              && SCpt(i)@S(ii1,i) = SCpt(i)@S(ii,i))
              => ii1 = ii )))).
Proof.
intro ii i Hap H.
expand exec@S(ii,i).
expand cond@S(ii,i).
intctxt Mneq.
exists j.
expand exec@S(ii1,i).
expand cond@S(ii1,i).
assert
 ( S(ii,i) < S(ii1,i) || S(ii,i) = S(ii1,i) || S(ii,i) > S(ii1,i) ) as H2.
case H2.

assert
 order(SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i)) = orderOk as M9.
assert
 ( S(ii,i) < pred(S(ii1,i)) || S(ii,i) = pred(S(ii1,i)) || S(ii,i) > pred(S(ii1,i)) ) as H2.
case H2.
use counterIncreaseBis with pred(S(ii1,i)),S(ii,i),i as H2.
case H2.
by use orderTrans with SCpt(i)@S(ii,i),SCpt(i)@pred(S(ii1,i)),SCpt(i)@S(ii1,i).
by use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i).

assert order(SCpt(i)@S(ii1,i),SCpt(i)@S(ii,i)) = orderOk as _.
assert
 ( S(ii1,i) < pred(S(ii,i)) || S(ii1,i) = pred(S(ii,i)) || S(ii1,i) > pred(S(ii,i)) ) as H2.
case H2.
use counterIncreaseBis with pred(S(ii,i)),S(ii1,i),i as H2.
case H2.
by use orderTrans with SCpt(i)@S(ii1,i),SCpt(i)@pred(S(ii,i)),SCpt(i)@S(ii,i).
by use orderStrict with SCpt(i)@S(ii1,i),SCpt(i)@S(ii,i).
Qed.

goal noreplayInv:
  forall (ii, ii1, i:index), happens(S(ii1,i),S(ii,i)) =>
    (exec@S(ii1,i) && S(ii,i) < S(ii1,i)
      => order(SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i)) = orderOk).
Proof.
intro ii ii1 i Hap H.
use counterIncreaseStrictly with ii1, i as M0.
assert (S(ii,i) = pred(S(ii1,i)) || S(ii,i) < pred(S(ii1,i))) as H1.
case H1.
use counterIncreaseBis with pred(S(ii1,i)),S(ii,i),i as H1.

nosimpl(executable S(ii1,i); 1: by auto).
by auto.
intro H2.
case H1.
by use orderTrans with SCpt(i)@S(ii,i), SCpt(i)@pred(S(ii1,i)),SCpt(i)@S(ii1,i).
by expand exec@S(ii1,i). 
by expand exec@S(ii1,i).
Qed.



goal noreplayNew:
  forall (ii, ii1, i:index), happens(S(ii1,i)) =>
    (exec@S(ii1,i) && S(ii,i) <= S(ii1,i)
     && SCpt(i)@S(ii,i)  =  SCpt(i)@S(ii1,i) => ii = ii1).
Proof.
intro ii ii1 i *.
assert (S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i)) as H1.
case H1.
use noreplayInv with ii, ii1, i as M1.
by use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i).
Qed.


goal monotonicity:
 forall (ii, ii1, i:index), happens(S(ii1,i),S(ii,i)) =>
   (exec@S(ii1,i) && exec@S(ii,i) &&
     order(SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i)) = orderOk
     => S(ii,i) < S(ii1,i)).
Proof.
intro ii ii1 i *.
assert
  (S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i) || S(ii,i) > S(ii1,i)) as H2.
case H2.
by use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii,i).

use noreplayInv with ii1, ii, i as M1.

use orderTrans with SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i), SCpt(i)@S(ii,i) as M2.

use orderStrict with SCpt(i)@S(ii,i),SCpt(i)@S(ii,i).
Qed.




(* I proved this lemma but I did not use it to prove the security properties given in Robert's thesis *)
goal lastUpdateServer_:
  forall (t:timestamp), forall (i:index), happens(t) =>
    ((SCpt(i)@t = SCpt(i)@init && forall (ii:index), happens(S(ii,i)) => t<S(ii,i))
     ||
     (exists jj:index, SCpt(i)@t = SCpt(i)@S(jj,i) && S(jj,i) <= t &&
       (forall (jj':index), happens(S(jj',i)) => (S(jj',i) <= S(jj,i) || t < S(jj',i))))).
Proof.
nosimpl(induction; intro IH0).
intro i.
case t.

(* 1/8 *)
subst t, init.
by left.

(* 2/8 *)
subst t, Plug(i1,j).
use IH0 with pred(Plug(i1,j)),i as H1.
case H1.
left.
by use H with ii.
right.
exists jj.
use H0 with jj' as H2.
by case H2.

(* 3/8 *)
subst t, Plug1(i1,j).
use IH0 with pred(Plug1(i1,j)),i as H1.
case H1.
left.
by use H with ii.
right.
exists jj.
use H0 with jj' as H2.
by case H2.

(* 4/8 *)
subst t, Press(i1,j).
use IH0 with pred(Press(i1,j)),i as H1.
case H1.
left.
by use H with ii.
right.
exists jj.
use H0 with jj' as H2.
by case H2.

(* 5/8 *)
subst t, Press1(i1,j).
use IH0 with pred(Press1(i1,j)),i as H1.
case H1.
left.
by use H with ii.
right.
exists jj.
use H0 with jj' as H2.
by case H2.

(* 6/8 - interesting case *)
subst t, S(ii,i1).
use IH0 with pred(S(ii,i1)),i as H1.
case H1.
(**)
assert (i=i1 || i<>i1) as H2.
case H2.
(* i = i1 *)
right.
by exists ii.
(* i <> i1 *)
left.
split.
case (if i=i1 then  snd(dec(snd(snd(input@S(ii,i1))),k(i1))) else
       SCpt(i)@pred(S(ii,i1))).
by use H with ii1.
(**)
assert (i=i1 || i<>i1) as H2.
case H2.
(* i = i1 *)
right.
by exists ii.
(* i <> i1 *)
right.
exists jj.
split.
by case (if i = i1 then snd(dec(snd(snd(input@S(ii,i1))),k(i1))) else
       SCpt(i)@pred(S(ii,i1))).
assert (jj = jj' || jj <> jj') as H2.
case H2.
use H0 with jj' as H2.
by case H2.

(* 7/8 *)
subst t, S1(ii,i1).
use IH0 with pred(S1(ii,i1)),i as H1.
case H1.
left.
by use H with ii1.
right.
exists jj.
use H0 with jj' as H2.
by case H2.

(* 8/8 *)
subst t, S2(ii).
use IH0 with pred(S2(ii)),i as H1.
case H1.
left.
by use H with ii1.
right.
exists jj.
use H0 with jj' as H2.
by case H2.
Qed.

goal lastUpdateServer :
  forall (i,ii:index), happens(S(ii,i)) =>
    (SCpt(i)@S(ii,i) = SCpt(i)@init 
     ||
     (exists (jj:index), SCpt(i)@S(ii,i) = snd(dec(snd(snd(input@S(jj,i))),k(i))))).
Proof.
intro i ii.
use lastUpdateServer_ with S(ii,i),i as H1.
case H1.
by left.
right.
by exists jj.
Qed.
