(*******************************************************************************
YUBIHSM

[1] R. Künnemann, "Foundations for analyzing security APIs in the symbolic and
computational model’, 2014.

Y   -> S   : <pid,<nonce,otp>>
S   -> HSM : <pid,kh>,<aead,otp>>
HSM -> S   : ctr
S   -> Y   : accept

with
- ks = keystream(kh,pid)
- aead = < senc(ks,k) XOR <k2,pid>, mac(<k2,pid>,k) >
- otp = senc(<sid,ctr>,npr,k2)

PUBLIC DATA
- kh, pid
SECRET DATA KNOWN BY EACH PARTY
- YubiKey: k, k2, sid, ctr
- Server: sid, ctr
- HSM: k, k2, sid

COMMENTS

- The last message "otp || nonce || hmac || status" is unclear and not modelled
at all and replaced by "accept".
It was also not modelled in [1].

- The otp is an encryption of a triple (sid, ctr, npr).
It is modelled here as a randomized encryption of a pair (sid, ctr).

- The AEAD is an encryption with a mac.
??? Here the mac is not modelled.

- ??? keystream

- In [1], they "over-approximate in the case that the Yubikey increases the
session token by allowing the adversary to instantiate the rule for any counter
value that is higher than the previous one".
Here, we model the incrementation by 1 of the counter.

- As in [1], we model the two counters (session and token counters) as a single
counter.

- Diff terms are here to model a real system and an ideal system.
The ideal system uses a different key k2'(i,j) for each generated otp.
The goal is to being able to use the intctxt tactic for the auth goal.
*******************************************************************************)
senc enc,dec

abstract startplug: message
abstract endplug: message
abstract startpress: message
abstract accept:message

abstract myZero : message
abstract mySucc : message -> message

abstract AEADinit : index -> message

(* public/secret id *)
abstract pid: index -> message
name sid: index -> message

(* public key handle kh to reference the AES master key k *)
abstract kh: index -> message
name k: index -> message
(* AES working key k2, stored inside the AEAD *)
name k2: index -> message
name k2': index -> index -> message

abstract keystream: message -> message -> message

(* random values *)
name nonce: index -> index -> message
name npr: index -> index -> message
name n: index -> message

(* counters *)
mutable YCtr(i:index) : message = myZero
mutable SCtr(i:index) : message = myZero

(* authentication server's database *)
mutable AEAD(i:index) : message = AEADinit(i)

channel cY
channel cS
channel cHSM

abstract orderOk: message
abstract order: message -> message -> message

(* When the key is plugged, the counter is incremented. *)
process yubikeyplug(i:index,j:index) =
  in(cY,x1);
  if x1 = startplug then
    YCtr(i) := succ(YCtr(i));
    out(cY,endplug)

(* When the key is pressed:
   - an otp is sent with the current value of the counter,
   - the counter is incremented. *)
process yubikeypress(i:index,j:index) =
  in(cY,x2);
  if x2 = startpress then
    let ctr = YCtr(i) in
    YCtr(i) := mySucc(YCtr(i));
    out(cY,<pid(i),<nonce(i,j),enc(<sid(i),ctr>,npr(i,j),diff(k2(i),k2'(i,j)))>>)

(* When the server receives a message:
   - it checks whether it corresponds to a pid in its database,
   - it retrieves the AEAD and kh associated to this pid and asks the HSM to
   decode the received otp,
   - it checks that the counter inside the otp (received from the HSM) is strictly
   greater than the counter associated to the token,
   - if so, this counter value is used to update the database. *)
process server(ii:index) =
  in(cS,x);
  try find i such that fst(x) = pid(i) in
    out(cS, <<pid(i),kh(i)>,<AEAD(i),snd(snd(x))>>);
    in(cS,xctr);
    if
      order(SCtr(i),xctr) = orderOk
    then
      SCtr(i) := xctr;
      out(cS,accept)

(* The attacker can read/write AEAD stored in the server's database. *)
process read_AEAD(ii:index) =
  out(cS,AEAD(ii))
process write_AEAD(ii:index) =
  in(cS,x3);
  try find i such that fst(x3) = pid(i) in
    AEAD(i) := snd(x3)

(* Model for the rule YSM_AEAD_YUBIKEY_OTP_DECODE of the HSM. *)
process YSM_AEAD_YUBIKEY_OTP_DECODE(ii:index) =
  in(cHSM,xdata);
  try find i such that fst(xdata) = <pid(i),kh(i)> in
    let aead = fst(snd(xdata)) in
    let otp = snd(snd(xdata)) in
    if
      dec(aead XOR <k2(i),pid(i)>,k(i)) <> fail
      && dec(aead XOR <k2(i),pid(i)>,k(i)) = keystream(kh(i),pid(i))
      && diff (dec(otp,k2(i)) <> fail && fst(dec(otp,k2(i))) = sid(i),
               exists (j:index),
                 dec(otp,k2'(i,j)) <> fail && fst(dec(otp,k2'(i,j))) = sid(i))
    then
      out(cHSM,
        diff (snd(dec(otp,k2(i))),
              try find j such that fst(dec(otp,k2'(i,j))) = sid(i) in
                snd(dec(otp,k2'(i,j))))).

system
  ( (!_i !_j Plug: yubikeyplug(i,j)) |
    (!_i !_j Press: yubikeypress(i,j)) |
    (!_ii Server: server(ii)) |
    (!_ii Read: read_AEAD(ii)) |
    (!_ii Write: write_AEAD(ii)) |
    (!_ii Decode: YSM_AEAD_YUBIKEY_OTP_DECODE(ii)) ).

axiom orderTrans (n1,n2,n3:message):
    (order(n1,n2) = orderOk && order(n2,n3) = orderOk)
    => order(n1,n3) = orderOk

axiom orderStrict(n1,n2:message): n1 = n2 => order(n1,n2) <> orderOk.

(* Authentication goal for the ideal system *)
goal [right] auth:
 forall (ii,i,ii':index),
  happens(Server1(ii,i),Decode(ii',i))
  =>
  ((cond@Server1(ii,i) && cond@Decode(ii',i))
    =>
    (exists (j:index),
    Press(i,j) < Decode(ii',i)
    && snd(snd(output@Press(i,j))) = snd(snd(input@Decode(ii',i))))).
Proof.
intro ii i ii' *.
expand cond@Decode(ii',i).
intctxt Mneq0.
exists j.
Qed.
