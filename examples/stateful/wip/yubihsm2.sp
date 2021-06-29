(*******************************************************************************
YUBIHSM

[1] R. Künnemann, "Foundations for analyzing security APIs in the symbolic and
computational model", 2014.

Y   -> S   : <pid,<nonce,otp>>
S   -> HSM : <pid,kh>,<aead,otp>>
HSM -> S   : ctr
S   -> Y   : accept

with
- aead = senc(<k,sid>,mkey)
- otp = senc(<sid,ctr>,npr,k)

PUBLIC DATA
- kh, pid
SECRET DATA KNOWN BY EACH PARTY
- YubiKey(pid): k(pid), sid(pid), ctr(pid)
- Server: { sid(pid), ctr(pid) | pid }
- HSM: mkey, { k(pid), sid(pid) | pid }

COMMENTS

- The last message "otp || nonce || hmac || status" is unclear and not modelled
at all and replaced by "accept".
It was also not modelled in [1].

- The otp is an encryption of a triple (sid, ctr, npr).
It is modelled here as a randomized encryption of a pair (sid, ctr).

- senc is assumed to be AEAD (we do not use the associated data)

- In [1], they "over-approximate in the case that the Yubikey increases the
session token by allowing the adversary to instantiate the rule for any counter
value that is higher than the previous one".
Here, we model the incrementation by 1 of the counter.

- As in [1], we model the two counters (session and token counters) as a single
counter.

- Diff terms are here to model a real system and two ideal systems.
  - the first intermediate ideal system replace key look-up in the 
    server database by the honest keys;
  - the fully ideal system uses a different key k2'(i,j) for each 
    generated otp. The goal is to being able to use the intctxt tactic for 
    the auth goal.
*******************************************************************************)
set autoIntro=false.

senc enc,dec

abstract startplug: message
abstract endplug: message
abstract startpress: message
abstract accept:message

(* counters initial value *)
abstract cinit : message
(* counter successor *)
abstract mySucc : message -> message

(* encoding of a public identity as a message *)
abstract mpid: index -> message

(* secret identity *)
name sid: index -> message

(* public key handle kh to reference the AES master key mkey *)
abstract kh: message
name mkey: message

(* working key k(pid) of yubikey `pid`, stored inside the AEAD *)
name k: index -> message
(* fully ideal version of `ki(pid)`, different for each session *)
name k': index -> index -> message

(* counters *)
mutable YCtr(i:index) : message = cinit
mutable SCtr(i:index) : message = cinit

(* random samplings used to initialized AEAD  *)
name rinit : index -> message
(* authentication server's database for each pid *)
mutable AEAD(pid:index) : message = enc(<k(pid), sid(pid)>, rinit(pid), mkey).

channel cY
channel cS
channel cHSM

(* Order over counters.
   Assumed transitive and strict later through axioms. *)
abstract (~<): message -> message -> boolean.

(* When the key is plugged for yubikey `pid`, the counter is incremented. *)
process yubikeyplug (pid:index) =
  in(cY,x1);
  YCtr(pid) := succ(YCtr(pid));
  out(cY,endplug).

name nonce : index -> index -> message
name npr : index -> index -> message

(* When the key is pressed on the `j`-th session of yubikey `pid`:
   - an otp is sent with the current value of the counter,
   - the counter is incremented. *)
process yubikeypress (pid:index,j:index) =
  in(cY,x2);  
  let ctr = YCtr(pid) in
  YCtr(pid) := mySucc(YCtr(pid));
  let menc = enc(<sid(pid),ctr>,npr(pid,j),k(pid)) in
  out(cY,<mpid(pid), <nonce(pid,j), menc>>).

(* fully idealized version of `yubikeypress`. *)
process yubikeypress_ideal (pid:index,j:index) =
  in(cY,x2);  
  let ctr = YCtr(pid) in
  YCtr(pid) := mySucc(YCtr(pid));
  let menc = enc(<sid(pid),ctr>,npr(pid,j),diff(k(pid),k'(pid,j))) in
  out(cY,<mpid(pid), <nonce(pid,j), menc>>).

(* When the server receives a message for pid:
   - it checks whether it corresponds to a pid in its database,
   - it retrieves the AEAD and kh associated to this pid and asks the HSM to
   decode the received otp,
   - it checks that the counter inside the otp (received from the HSM) is strictly
   greater than the counter associated to the token,
   - if so, this counter value is used to update the database. *)
process server (pid:index) =
  in(cS,x);
  out(cHSM, <<mpid(pid),kh>,<AEAD(pid),x>>);
  in(cHSM,xctr);
  if SCtr(pid) ~< xctr then
  SCtr(pid) := xctr;
  out(cS,accept).

(* The attacker can read/write AEAD stored in the server's database. *)
process read_AEAD (pid:index) =
  out(cS,AEAD(pid)).

process write_AEAD (pid:index)=
  in(cS,x);
  AEAD(pid) := x.

(* Model for the rule YSM_AEAD_YUBIKEY_OTP_DECODE of the HSM. *)
process YSM_AEAD_YUBIKEY_OTP_DECODE (pid:index) =
  in(cHSM,xdata);
  if fst(xdata) = <mpid(pid),kh> then
    let aead = fst(snd(xdata)) in
    let otp = snd(snd(xdata)) in

    let aead_dec = dec(aead,mkey) in    
    let k_pid   = diff(fst(aead_dec), k(pid)) in
    let sid_pid = diff(snd(aead_dec), sid(pid)) in

    let otp_dec = dec(otp,k_pid) in

    if aead_dec <> fail && otp_dec <> fail && fst(otp_dec) = sid_pid
    then
      out(cHSM, snd(otp_dec)).

(* fully idealized version of `YSM_AEAD_YUBIKEY_OTP_DECODE`. *)
process YSM_AEAD_YUBIKEY_OTP_DECODE_ideal (pid:index) =
  in(cHSM,xdata);
  if fst(xdata) = <mpid(pid),kh> then
    let aead = fst(snd(xdata)) in
    let otp = snd(snd(xdata)) in

    let aead_dec = dec(aead,mkey) in    
    let otp_dec = dec(otp,k(pid)) in

    if aead_dec <> fail && 
       diff( otp_dec <> fail && fst(otp_dec) = sid(pid),
             exists (j:index),
             dec(otp,k'(pid,j)) <> fail &&
             fst(dec(otp,k'(pid,j))) = sid(pid))
    then
      out(cHSM, 
          diff( snd(otp_dec),
                try find j such that 
                  dec(otp,k'(pid,j)) <> fail && 
                  fst(dec(otp,k'(pid,j))) = sid(pid)
                in
                snd(dec(otp,k'(pid,j))))).

(* base system with middle system *)
system [BtoM]
  ( (!_pid !_j Plug   : yubikeyplug(pid)                 ) |
    (!_pid !_j Press  : yubikeypress(pid,j)              ) |
    (!_pid !_j Server : server(pid)                      ) |
    (!_pid !_j Read   : read_AEAD(pid)                   ) |
    (!_pid !_j Write  : write_AEAD(pid)                  ) |
    (!_pid !_j Decode : YSM_AEAD_YUBIKEY_OTP_DECODE(pid) )).

(* middle system with ideal system *)
system [MtoI]
  ( (!_pid !_j Plug   : yubikeyplug(pid)                       ) |
    (!_pid !_j Press  : yubikeypress_ideal(pid,j)              ) |
    (!_pid !_j Server : server(pid)                            ) |
    (!_pid !_j Read   : read_AEAD(pid)                         ) |
    (!_pid !_j Write  : write_AEAD(pid)                        ) |
    (!_pid !_j Decode : YSM_AEAD_YUBIKEY_OTP_DECODE_ideal(pid) )).

(* TODO: allow to have axioms for all systems *)
axiom [MtoI] orderTrans (n1,n2,n3:message): n1 ~< n2 => n2 ~< n3 => n1 ~< n3.

(* TODO: allow to have axioms for all systems *)
axiom [MtoI] orderStrict(n1,n2:message): n1 = n2 => n1 ~< n2 => False.

(* Authentication goal for the fully idealized system *)
goal [right:MtoI] auth (pid,j0,j1:index):
  happens(Server1(pid,j0),Decode(pid,j1)) =>
  cond@Server1(pid,j0) => cond@Decode(pid,j1) =>
  exists (j2:index),
  Press(pid,j2) < Decode(pid,j1)
  && snd(snd(output@Press(pid,j2))) = snd(snd(input@Decode(pid,j1))).
Proof.
intro Hap @/cond HcS [HcD1 [j3 [HcD3 HcD4]] HcD5].
expandall.
intctxt HcD3 => // _ H [_ _].
by exists j3. 
Qed.
