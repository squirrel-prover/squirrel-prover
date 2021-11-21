(*******************************************************************************
YUBIKEY

[1] R. Künnemann, "Foundations for analyzing security APIs in the symbolic and
computational model’, 2014.

C -> S : pid || otp || nonce
S -> C : otp || nonce || hmac || status

COMMENTS
- The last message is unclear and not modelled at all and replaced by "accept".
It was also not modelled in the Tamarin/Sapic file provided in [1].

- otp is an encryption of a triple (secret(i), cpt, npr(i,j)).
It is modelled here as a randomized encryption of a pair (secret(i), cpt).
According to the specification in [1], AES is used.

- In [1], they "over-approximate in the case that the Yubikey increases the
session token by allowing the adversary to instantiate the rule for any counter
value that is higher than the previous one".
Here, we model the incrementation by 1 of the counter.

HELPING LEMMAS
- counter increase

SECURITY PROPERTIES 
The 3 security properties as stated in [1].
- Property 1: no replay counter
- Property 2: injective correspondence
- Property 3: monotonicity
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

(* When the key is plugged, its counter is incremented. *)

process yubikeyplug(i:index,j:index) =
  in(cT, x1);
  if x1 = startplug then YCpt(i) := mySucc(YCpt(i)); out(cT,endplug)

(* When the key is pressed, an otp is sent with the current value of the 
counter and the counter is imcremented. *)

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

include Basic.

goal dec_enc (x,y,z:message) : dec(enc(x,z,y),y) = x.
Proof. auto. Qed.
hint rewrite dec_enc.

(* f_apply *)

goal fst_apply (x,y : message) : x = y => fst(x) = fst(y).
Proof. auto. Qed.

goal snd_apply (x,y : message) : x = y => snd(x) = snd(y).
Proof. auto. Qed.

goal dec_apply (x,y,x1,y1 : message) : 
 x = y => x1 = y1 => dec(x,x1) = dec(y,y1).
Proof. auto. Qed.


(* AXIOMS *)

axiom orderTrans (n1,n2,n3:message):
  n1 ~< n2 = orderOk => n2 ~< n3 = orderOk => n1 ~< n3 = orderOk.

axiom orderStrict (n1,n2:message):
  n1 = n2 => n1 ~< n2 <> orderOk.
  
axiom orderSucc (n1,n2:message):
  n1 = n2 => n1 ~< mySucc(n2) = orderOk.

(* HELPING LEMMAS *)

(* Some properties on the counter on the server side. *)

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

(* The counter SCpt(i) increases (not strictly) between t' and t when t' < t. *)
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

(* SECURITY PROPERTIES *)

(* Property 1: no replay, relying on an invariant. *)

goal noreplayInv (ii, ii1, i:index):
   happens(S(ii1,i),S(ii,i)) =>
   exec@S(ii1,i) && S(ii,i) < S(ii1,i) => 
   SCpt(i)@S(ii,i) ~< SCpt(i)@S(ii1,i) = orderOk.
Proof.
  intro Hap [Hexec Ht].
  use counterIncreaseStrictly with ii1, i as M0 => //.
  assert (S(ii,i) = pred(S(ii1,i)) || S(ii,i) < pred(S(ii1,i))) as H1
  by constraints.
  case H1.

  (* case S(ii,i) = pred(S(ii1,i)) *)
  congruence.

  (* case S(ii,i) < pred(S(ii1,i)) *)
  use counterIncreaseBis with pred(S(ii1,i)),S(ii,i),i as H2 => //.
  case H2 => //.
  by apply orderTrans _ (SCpt(i)@pred(S(ii1,i))) _.
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


(* Property 2: injective correspondence as stated in [1]. *)

goal injective_correspondence (ii,i:index):
   happens(S(ii,i)) =>
   exec@S(ii,i) =>
     exists (j:index),
       Press(i,j) < S(ii,i) && cpt(i,j)@Press(i,j) = SCpt(i)@S(ii,i)
&& 
       forall (ii1:index), happens(S(ii1,i)) =>
            exec@S(ii1,i) =>
            cpt(i,j)@Press(i,j) = SCpt(i)@S(ii1,i) => ii1 = ii.

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
  assert (cpt(i,j)@Press(i,j) = SCpt(i)@S(ii,i)) => //.

  intro ii' Hap' Hexec'.
  intro Eq => //. 
  assert (SCpt(i)@S(ii,i) = SCpt(i)@S(ii',i)) => //.
  assert (S(ii,i) = S(ii',i) || S(ii,i) < S(ii',i) || S(ii,i) > S(ii',i)) => //.
  case H => //.

    (* 1st case: S(ii,i) < S(ii',i) *)
    assert (S(ii,i) = pred(S(ii',i)) || S(ii,i) < pred(S(ii',i))) => //.
    case H0 => //.

      (* S(ii,i) = pred(S(ii',i) < S(ii',i) *)
      use counterIncreaseStrictly with ii',i => //.
      subst  S(ii,i), pred(S(ii',i)) => //.
      by use orderStrict with SCpt(i)@pred(S(ii',i)), SCpt(i)@S(ii',i) => //.

      (* S(ii,i) < pred(S(ii',i))  < S(ii',i) *)
      use counterIncreaseStrictly with ii',i => //.
      use counterIncreaseBis with pred(S(ii',i)), S(ii,i), i => //.
      case H1.
        use orderTrans with SCpt(i)@S(ii,i), SCpt(i)@pred(S(ii',i)), SCpt(i)@S(ii',i) => //.
        by use orderStrict with SCpt(i)@S(ii,i), SCpt(i)@S(ii',i) => //.

        subst SCpt(i)@pred(S(ii',i)), SCpt(i)@S(ii,i).
        by use orderStrict with SCpt(i)@S(ii,i), SCpt(i)@S(ii',i) => //.

    (* 2nd case: S(ii,i) > S(ii',i) *)
    assert (pred(S(ii,i)) = S(ii',i) || pred(S(ii,i)) > S(ii',i)) => //.
    case H0 => //.

      (* S(ii,i) > pred(S(ii,i)) = S(ii',i) *)
      use counterIncreaseStrictly with ii,i => //.
      subst S(ii',i), pred(S(ii,i)).
      by use orderStrict with SCpt(i)@pred(S(ii,i)), SCpt(i)@S(ii,i) => //.

      (* S(ii,i) > pred(S(ii,i)) >  S(ii',i) *)
      use counterIncreaseStrictly with ii,i => //.
      use counterIncreaseBis with pred(S(ii,i)), S(ii',i), i => //.
      case H1.
        use orderTrans with SCpt(i)@S(ii',i), SCpt(i)@pred(S(ii,i)), SCpt(i)@S(ii,i) => //.
        by use orderStrict with SCpt(i)@S(ii',i), SCpt(i)@S(ii,i) => //.


        subst SCpt(i)@pred(S(ii,i)), SCpt(i)@S(ii',i).
        by use orderStrict with SCpt(i)@S(ii',i), SCpt(i)@S(ii,i) => //.
Qed.


(* Property 3: monotonicity. *)

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

