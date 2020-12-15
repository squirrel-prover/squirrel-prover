(*******************************************************************************
YUBIKEY

C -> S: pid || otp || nonce
S -> C: otp || nonce || hmac || status 
This last message is unclear and not modelled at all. I simply output ok.
It was not modelled in the Tamarin file.
*******************************************************************************)
senc enc,dec

abstract startplug: message
abstract endplug: message
abstract startpress: message
abstract accept:message

abstract myZero : message
abstract mySucc : message->message
abstract myPred : message->message


abstract pid : index -> message
name k: index -> message
name secret: index -> message
name nonce: index->index->message
name npr: index->index->message

mutable YCpt: index->message
mutable SCpt: index->message

channel cT
channel cR

axiom stateYubikeyInit : forall (i:index), YCpt(i)@init = myZero

axiom stateServerInit : forall (i:index), SCpt(i)@init = myZero

abstract orderOk : message
abstract order : message->message->message

axiom orderSucc : forall (n:message), order(n,mySucc(n)) = orderOk


axiom orderTrans :
  forall (n1,n2,n3:message),
    (order(n1,n2) = orderOk && order(n2,n3) = orderOk)
    => order(n1,n3) = orderOk

axiom orderStrict : forall (n1,n2:message), n1 = n2 => order(n1,n2) <> orderOk



process yubikeyplug(i:index,j:index) =
  in(cT, x1);
  if x1 = startplug then YCpt(i) := succ(YCpt(i)); out(cT,endplug) 


process yubikeypress(i:index,j:index) =
  in(cT,x2);
  if x2 = startpress then  
       let cpt = YCpt(i) in 
       YCpt(i) := mySucc(YCpt(i)); 
       out(cT,<pid(i),<nonce(i,j),enc(cpt,npr(i,j),k(i))>>)


(* HELP !! remettre le chiffrement d'une paire et comment appliquer intctxt *)

process server(ii:index) =
  in(cR,y1); 
   try find  i such that fst(y1) = pid(i) in
     if  dec(snd(snd(y1)),k(i)) <> fail && order(SCpt(i),dec(snd(snd(y1)),k(i))) =orderOk then
     SCpt(i) := dec(snd(snd(y1)),k(i)); 
     out(cR,accept)


system ((!_i !_j Plug: yubikeyplug(i,j)) | (!_i !_j Press: yubikeypress(i,j)) | (!_ii S: server(ii))).


(* Je m'inspire de slk06.sp *)

goal lastUpdateServer_:
forall (t:timestamp), forall (i:index), (SCpt(i)@t = SCpt(i)@init && forall (ii:index), t<S(ii,i))
 ||
(exists jj:index, SCpt(i)@t = SCpt(i)@S(jj,i) && S(jj,i) <= t &&
(forall (jj':index), S(jj',i) <= S(jj,i) || t < S(jj',i))).
Proof.
induction.
case t.
case H0.

(* 1 /8 *)
substitute t, Plug(i1,j).
apply IH0 to pred(Plug(i1,j)).
apply H0 to i.
case H1.
left.
apply H1 to ii.
right.
exists jj.
apply H1 to jj'.
case H2.

(* 2/8 *)
substitute t, Plug1(i1,j).
apply IH0 to pred(Plug1(i1,j)).
apply H0 to i.
case H1.
left.
apply H1 to ii.
right.
exists jj.
apply H1 to jj'.
case H2.

(* 3/8 *)
substitute t, Press(i1,j).
apply IH0 to pred(Press(i1,j)).
apply H0 to i.
case H1.
left.
apply H1 to ii.
right.
exists jj.
apply H1 to jj'.
case H2.

(* 4/8 *)
substitute t, Press1(i1,j).
apply IH0 to pred(Press1(i1,j)).
apply H0 to i.
case H1.
left.
apply H1 to ii.
right.
exists jj.
apply H1 to jj'.
case H2.

(* interesting case *)
substitute t, S(ii,i1).
apply IH0 to pred(S(ii,i1)).
apply H0 to i.
case H1.
(**)
assert (i=i1 || i<>i1).
case H2.
(* i = i1 *)
right.
exists ii.
(* i <> i1 *)
left.
split.
case (if i=i1 then  dec(snd(snd(input@S(ii,i1))),k(i1)) else
       SCpt(i)@pred(S(ii,i1))).
apply H1 to ii1.
(**)
assert (i=i1 || i<>i1).
case H2.
(* i = i1 *)
right.
exists ii.
(* i <> i1 *)
right.
exists jj.
split.
case (if i = i1 then dec(snd(snd(input@S(ii,i1))),k(i1)) else
       SCpt(i)@pred(S(ii,i1))).
assert (jj = jj' || jj <> jj').
case H2.
apply H1 to jj'.
case H2.

(* 5/8 *)
substitute t, S1(ii,i1).
apply IH0 to pred(S1(ii,i1)).
apply H0 to i.
case H1.
left.
apply H1 to ii1.
right.
exists jj.
apply H1 to jj'.
case H2.

(* 6/8 *)
substitute t, S2(ii).
apply IH0 to pred(S2(ii)).
apply H0 to i.
case H1.
left.
apply H1 to ii1.
right.
exists jj.
apply H1 to jj'.
case H2.

(* 7/ 8*)
substitute t, init.
left.
Qed.

goal lastUpdateServer :
forall (i,ii:index), SCpt(i)@S(ii,i) = SCpt(i)@init || 
(exists (jj:index), SCpt(i)@S(ii,i) = dec(snd(snd(input@S(jj,i))),k(i))).
Proof.
intros.
apply lastUpdateServer_ to S(ii,i).
apply H0 to i.
case H1.
left.
right.
exists jj.
Qed.




(* I expressed a non-injective version of authentication but since the encryption outputted by the yubikey contains a random number, I think that this property will imply the injective one *)

goal auth:
   forall (ii,i:index), cond@S(ii,i) => 
    (exists (j:index), Press(i,j) < S(ii,i) && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i)))).
Proof.
intros.
expand cond@S(ii,i).
intctxt M1.
exists j.
Qed.



goal monotonicity:
  forall (ii1,ii2,i:index), (cond@S(ii1,i) && cond@S(ii2,i) && 
     order(SCpt(i)@S(ii1,i),SCpt(i)@S(ii2,i)) = orderOk 
     => S(ii1,i) < S(ii2,i)). 
Proof.
intros.
expand cond@S(ii,i).
expand cond@S(ii1,i).
substitute (dec(snd(snd(input@S(ii,i))),k(i))),  SCpt(i)@S(ii,i).
substitute (dec(snd(snd(input@S(ii1,i))),k(i))),  SCpt(i)@S(ii1,i).
admit.
Qed.



goal noreplayNew: 
  forall (ii1, ii2, i:index),   exec@S(ii2,i) && S(ii1,i) <= S(ii2,i) 
     && SCpt(i)@S(ii1,i)  =  SCpt(i)@S(ii2,i) => ii1 = ii2.
Proof.
intros.
assert(S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i)).
case H1.
apply lastUpdateServer to ii1, i.
case H1.


executable S(ii1,i).
apply H1 to S(ii,i).
expand exec@S(ii,i).
expand cond@S(ii,i).

expand exec@S(ii1,i). 
expand cond@S(ii1,i).
intctxt M3.
intctxt M6.


case H4.

admit.
Qed.



(* The counter SCpt(i) strictly increases when t is an action S performed by the the server with tag i. Otherwise, this value remains unchanged at this step. *)
goal counterIncrease:
forall (t:timestamp), forall (i:index), (t > init && exec@t) => (
((exists ii:index, t=S(ii,i)) && order(SCpt(i)@pred(t),SCpt(i)@t) = orderOk) 
|| ((not exists ii:index, (t = S(ii,i))) && (SCpt(i)@pred(t) = SCpt(i)@t))).
Proof.
intros.
apply orderSucc to SCpt(i)@pred(t).
case t.
case H1.
right.
right.
right.
right.
(* cas difficile *)
assert(i = i1 || i<> i1).
(* i = i1 *)
case H1.
left.
substitute t, S(ii,i).
split.
exists ii.
expand SCpt(i)@S(ii,i).
expand exec@S(ii,i).
expand cond@S(ii,i).
(* i <> i1 *)
right.
substitute t, S(ii,i1).
admit. (* HELP !! je ne sais pas quoi dire pour conclure mais le raisonnement est a priori ok *)
(* fin cas difficile *)
right.
right.
Qed.



(* The counter SCpt(i) strictly increases when t is an action S performed by the server with tag i. *)
goal counterIncreaseBis:
forall (t:timestamp), forall (t':timestamp),  forall (i:index), (exec@t && t' < t) => 
(((exists ii:index, t=S(ii,i)) && order(SCpt(i)@t',SCpt(i)@t) = orderOk) 
|| ((not exists ii:index, (t = S(ii,i))) && (SCpt(i)@t' = SCpt(i)@t))).


Proof.
induction.
apply IH0 to pred(t).
assert (t' >= pred(t) || t' <pred(t)).
case H2.

(* case t' >= pred(t) *)
assert t' = pred(t).
apply counterIncrease to t.
apply H2 to i.
substitute pred(t), t'.

(* case t' < pred(t) *)
apply H1 to t'.
apply H2 to i.

case t.
case H2.
right.
substitute t, Plug(i1,j).

apply H1 to t'.
apply counterIncrease to t.

apply H4 to i.
case H5.
case t.
case H6.
right.

case H4.
left.

assert(order(SCpt(i)@t',SCpt(i)@t) = orderOk).

apply orderTrans to SCpt(i)@t',SCpt(i)@pred(t),SCpt(i)@t.
case H4.
executable t.
apply H3 to pred(t).

(* case t' >= pred(t) *)
assert t' = pred(t).
apply counterIncrease to t.
apply H2 to i.
substitute pred(t), t'.
Qed.



goal counterIncreaseTer:
forall (t:timestamp), forall (t':timestamp),  forall (ii,i:index), (exec@t && t' < t && t=S(ii,i)) 
=> (order(SCpt(i)@t', SCpt(i)@t) = orderOk).
Proof.
admit.
Qed.

goal noreplay: 
  forall (ii1, ii2, i:index),  cond@S(ii1,i) && cond@S(ii2,i) 
     && dec(snd(snd(input@S(ii1,i))),k(i)) =  dec(snd(snd(input@S(ii2,i))),k(i)) => ii1 = ii2. 
Proof.
admit.
Qed.


goal noreplayNew: 
  forall (ii1, ii2, i:index),   exec@S(ii2,i) && S(ii1,i) <= S(ii2,i) 
     && SCpt(i)@S(ii1,i)  =  SCpt(i)@S(ii2,i) => ii1 = ii2.
Proof.
intros.
assert(S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i)).
case H1.
apply counterIncreaseBis to S(ii1,i).
apply H1 to S(ii,i).
apply H2 to i.

executable S(ii1,i).
apply H4 to S(ii,i).
expand exec@S(ii,i).
expand cond@S(ii,i).

expand exec@S(ii1,i). 
expand cond@S(ii1,i).
intctxt M2.
intctxt M5.


case H4.

admit.
Qed.


goal monotonicity:
  forall (ii1,ii2,i:index), (cond@S(ii1,i) && cond@S(ii2,i) && order(SCpt(i)@S(ii1,i),SCpt(i)@S(ii2,i)) = orderOk 
     => S(ii1,i) < S(ii2,i)). 
Proof.
intros.
expand cond@S(ii,i).
expand cond@S(ii1,i).
substitute snd(dec(snd(snd(input@S(ii,i))),k(i))),  SCpt(i)@S(ii,i).
substitute snd(dec(snd(snd(input@S(ii1,i))),k(i))),  SCpt(i)@S(ii1,i).
admit.
Qed.
