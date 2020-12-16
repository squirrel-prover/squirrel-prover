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
by fst(dec(snd(snd(y1)),k(i))) = secret(i)"  I an unable to apply intctxt and to prove the goal auth *)
process server(ii:index) =
  in(cR,y1); 
   try find  i such that fst(y1) = pid(i) in
     if  dec(snd(snd(y1)),k(i)) <> fail && order(SCpt(i),snd(dec(snd(snd(y1)),k(i)))) =orderOk then
     SCpt(i) := snd(dec(snd(snd(y1)),k(i))); 
     out(cR,accept)


system ((!_i !_j Plug: yubikeyplug(i,j)) | (!_i !_j Press: yubikeypress(i,j)) | (!_ii S: server(ii))).




(* I expressed a non-injective version of authentication but since the encryption outputted by the yubikey contains a random number, I think that this property will imply the injective one *)
(* This is one of the property stated by Robert *)
goal auth:
   forall (ii,i:index), cond@S(ii,i) => 
    (exists (j:index), Press(i,j) < S(ii,i) && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i)))).
Proof.
intros.
expand cond@S(ii,i).
intctxt M1.
exists j.
Qed.



(* The counter SCpt(i) strictly increases when t is an action S performed by the the server with tag i. *)
goal counterIncreaseStrictly:
forall (ii,i:index), cond@S(ii,i) => order(SCpt(i)@pred(S(ii,i)),SCpt(i)@S(ii,i)) = orderOk.
Proof.
intros.
expand cond@S(ii,i).
Qed.


(* The counter SCpt(i) increases (not strictly) between pred(t) and t *)
goal counterIncrease:
forall (t:timestamp), forall (i:index), (t > init && exec@t) => 
(order(SCpt(i)@pred(t),SCpt(i)@t) = orderOk || SCpt(i)@pred(t) = SCpt(i)@t).
Proof.
intros.
case t.
case H1.
right.
right.
right.
right.

assert(i = i1 || i <>i1).
case H1.
(* i = i1 *)
left.
substitute t, S(ii,i).
expand exec@S(ii,i).
apply counterIncreaseStrictly to ii, i.
(* i <>i1 *)
right.
case(if i = i1 then snd(dec(snd(snd(input@S(ii,i1))),k(i1))) else
       SCpt(i)@pred(S(ii,i1))).
right.
right.
Qed.


(* The counter SCpt(i) increases (not strictly) between t' and t when t' < t *)
goal counterIncreaseBis:
forall (t:timestamp), forall (t':timestamp),  forall (i:index), (exec@t && t' < t) => 
(order(SCpt(i)@t',SCpt(i)@t) = orderOk || SCpt(i)@t' = SCpt(i)@t).


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
executable t.
apply H3 to pred(t).
apply H2 to i.

apply counterIncrease to t.
apply H6 to i.
case H5.
case H6.

(* 1/2 *)
left.
apply orderTrans to SCpt(i)@t',SCpt(i)@pred(t),SCpt(i)@t.

(* 2/2 *)
case H6.
Qed.


goal noreplayInv:
  forall (ii, ii1, i:index),    exec@S(ii1,i) && S(ii,i) < S(ii1,i) 
     => order(SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i)) = orderOk.
Proof.
intros.
apply counterIncreaseStrictly to ii1, i.
apply counterIncreaseBis to pred(S(ii1,i)).
apply H1 to S(ii,i).

executable S(ii1,i).
apply H3 to pred(S(ii1,i)).
assert(S(ii,i) = pred(S(ii1,i)) || S(ii,i) < pred(S(ii1,i))).
case H5.

apply H2 to i.
case H5.
apply orderTrans to SCpt(i)@S(ii,i), SCpt(i)@pred(S(ii1,i)),SCpt(i)@S(ii1,i).

expand exec@S(ii1,i).
Qed.



goal noreplayNew: 
  forall (ii, ii1, i:index),   exec@S(ii1,i) && S(ii,i) <= S(ii1,i) 
     && SCpt(i)@S(ii,i)  =  SCpt(i)@S(ii1,i) => ii = ii1.
Proof.
intros.
assert(S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i)).
case H1.
apply noreplayInv to ii, ii1, i.
apply orderStrict to SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i).
Qed.



goal monotonicity:
 forall (ii, ii1, i:index),   exec@S(ii1,i) && exec@S(ii,i) &&
     order(SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i)) = orderOk 
     => S(ii,i) < S(ii1,i). 
Proof.
intros.
assert(S(ii,i) = S(ii1,i) || S(ii,i) < S(ii1,i) || S(ii,i) > S(ii1,i)).
case H2.
apply orderStrict to SCpt(i)@S(ii,i),SCpt(i)@S(ii,i).

apply noreplayInv to ii1, ii, i.

apply orderTrans to SCpt(i)@S(ii,i),SCpt(i)@S(ii1,i), SCpt(i)@S(ii,i).

apply orderStrict to SCpt(i)@S(ii,i),SCpt(i)@S(ii,i).
Qed.




(* I proved this lemma but I did not use it to prove the security properties given in Robert's thesis *)
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
case (if i=i1 then  snd(dec(snd(snd(input@S(ii,i1))),k(i1))) else
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
case (if i = i1 then snd(dec(snd(snd(input@S(ii,i1))),k(i1))) else
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
(exists (jj:index), SCpt(i)@S(ii,i) = snd(dec(snd(snd(input@S(jj,i))),k(i)))).
Proof.
intros.
apply lastUpdateServer_ to S(ii,i).
apply H0 to i.
case H1.
left.
right.
exists jj.
Qed.



