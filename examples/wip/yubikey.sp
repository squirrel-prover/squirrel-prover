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
       out(cT,<pid(i),<nonce(i,j),enc(<secret(i),cpt>,npr(i,j),k(i))>>)


process server(ii:index) =
  in(cR,y1); 
   try find  i such that fst(y1) = pid(i) in
     if  order(SCpt(i),snd(dec(snd(snd(y1)),k(i)))) =orderOk then
     SCpt(i) := snd(dec(snd(snd(y1)),k(i))); 
     out(cR,accept)


system ((!_i !_j Plug: yubikeyplug(i,j)) | (!_i !_j Press: yubikeypress(i,j)) | (!_ii S: server(ii))).

goal noreplay: 
   forall (ii1, ii2, i:index), cond@S(ii1,i) && cond@S(ii2,i) 
     && snd(dec(snd(snd(input@S(ii1,i))),k(i))) =  snd(dec(snd(snd(input@S(ii2,i))),k(i))) => ii1 = ii2. 

Proof.
admit.
Qed.


(* I expressed a non-injective version of authentication but since the encryption outputted by the yubikey contains a random number, I think that this property will imply the injective one *)

goal auth:
   forall (ii,i:index), cond@S(ii,i) => 
    (exists (j:index), Press(i,j) < S(ii,i) && snd(snd(output@Press(i,j))) = snd(snd(input@S(ii,i)))).
Proof.
intros.
expand cond@S(ii,i).

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
