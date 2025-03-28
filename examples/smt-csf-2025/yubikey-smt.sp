(**
# YUBIKEY

The YubiKey is a simple physical authentication device with a unique button.
This device, manufactured by Yubico, allows users to securely authenticate to
their accounts by issuing a one-time password (OTP).

In its typical configuration, the YubiKey generates a random OTP by encrypting
a secret value and a counter.
This message is accepted by the server only if it decrypts under the correct
key to a valid secret value containing a counter whose value is larger than the
last value accepted by the server for that YubiKey.

In this model, we analyze the security of the protocol as described in [1],
assuming that the server remains secure.

Yubico assigns a key `k`, as well as a public and a secret identifier `pid, sid`
to each YubiKey. The counter `cpt` inside the YubiKey is incremented whenever the
YubiKey is plugged in, as well as when an OTP is generated, i.e. when the button
of the YubiKey is pressed. This OTP is obtained by encrypting the counter value
and the `sid` of the YubiKey with the key `k`.

* YubiKey -> Server : <pid,<nonce,senc(<sid,cpt>,npr,k)>>

Here, `npr` is the encryption randomness. The server accepts this message if it
decrypts with a legitimate key `k`, and leads to a valid secret value `sid`.
Lastly, the counter value obtained through decryption has to be larger than the
current value stored in the server database. After this exchange, the server
updates its counter with the value just received.

#### COMMENTS

* The OTP is an encryption of a triple `<sid, cpt, npr>`.
It is modelled here as a randomized encryption of a pair `<sid, cpt>`.
According to the specification in [1], AES is used.

* In [1], they "over-approximate in the case that the Yubikey increases the
session token by allowing the adversary to instantiate the rule for any counter
value that is higher than the previous one".
Here, we model the incrementation by 1 of the counter.

#### SECURITY PROPERTIES

The 3 security properties as stated in [1].

* Property 1: absence of replay attacks.
* Property 2: injective correspondence.
* Property 3: monotonicity.

[1] R. Künnemann, "Foundations for analyzing security APIs in the symbolic and
computational model’, 2014.*)

set timeout=12.

(** Public constants (`abstract`) and names used in the protocol. *)
abstract startplug  : message
abstract endplug    : message
abstract startpress : message
abstract accept     : message
abstract pid        : index -> message

name sid  : index -> message
name nonce: index * index -> message.

(**
Symmetric encryption scheme, using the secret key `k` (with index arity 1
so that each YubiKey is associated to a key) and the random `npr` (with index
arity 2 so that each session of a YubiKey uses a new random name).
*)
senc enc,dec
name k  : index -> message
name npr: index * index -> message.

(**
Public constants and public functions used to model counter values.
*)
abstract myzero  : message
abstract myone   : message
abstract mySucc  : message -> message
abstract orderOk : message
abstract (~<)    : message -> message -> message.

(**
Mutable cells for the YubiKey and the server, initialized with `myzero`.
*)

mutable YCpt(i:index): message = myzero
mutable SCpt(i:index): message = myzero.

(** Communication channels used in the protocol. *)
channel cT
channel cR.

(** When the key is plugged, its counter is incremented. *)
process yubikeyplug(i:index,j:index) =
  in(cT, x1);
  if x1 = startplug then
    YCpt(i) := mySucc(YCpt(i));
    out(cT,endplug).

(** When the key is pressed, an OTP is sent with the current value of the
counter and the counter is incremented. *)
process yubikeypress(i:index,j:index) =
  in(cT,x2);
  if x2 = startpress then
    let cpt = YCpt(i) in
    YCpt(i) := mySucc(YCpt(i));
    out(cT,<pid(i),<nonce(i,j),enc(<sid(i),cpt>,npr(i,j),k(i))>>).

(** When the server receives a message, it checks whether it corresponds
to a pid in its database, and checks also that the counter inside the OTP
is strictly greater than the counter associated to the token.
If so, the value inside the OTP is used to update the database.
Now, the counter value associated to this token is this new value. *)
process server(ii:index) =
  in(cR,y1);
  try find i such that fst(y1) = pid(i) in
    (if dec(snd(snd(y1)),k(i)) <> fail
        && SCpt(i) ~< snd(dec(snd(snd(y1)),k(i))) = orderOk
    then
      SCpt(i) := snd(dec(snd(snd(y1)),k(i)));
      out(cR,accept)).

(** In the final system, processes can play in parallel an unbounded number
of sessions. *)
system
  ((!_i !_j Plug: yubikeyplug(i,j))
    | (!_i !_j Press: yubikeypress(i,j))
    | (!_ii S: server(ii))).


(** #### LIBRARIES

We include here some libraries, useful to help the tool with automated
reasoning. *)

include Real.

lemma [any] dec_enc (x,y,z:message) : dec(enc(x,z,y),y) = x.
Proof. auto. Qed.
hint rewrite dec_enc.

lemma [any]  fst_apply (x,y : message) : x = y => fst(x) = fst(y).
Proof. auto. Qed.

lemma [any]  snd_apply (x,y : message) : x = y => snd(x) = snd(y).
Proof. auto. Qed.

lemma dec_apply (x,y,x1,y1 : message) :
 x = y => x1 = y1 => dec(x,x1) = dec(y,y1).
Proof. auto. Qed.

(** #### AXIOMS

The following axioms are used to reason on counter values. *)

axiom [any] orderTrans (n1,n2,n3:message):
  n1 ~< n2 = orderOk => n2 ~< n3 = orderOk => n1 ~< n3 = orderOk.

axiom [any] orderStrict (n1,n2:message):
  n1 = n2 => n1 ~< n2 <> orderOk.

axiom [any] orderSucc (n1,n2:message):
  n1 = n2 => n1 ~< mySucc(n2) = orderOk.

hint smt orderTrans.
hint smt orderStrict.
hint smt orderSucc.

(** #### HELPING LEMMAS

We now prove some properties on the counter on the server side, used later
in the proofs of the security properties. 

******************************************************)

(** The counter `SCpt(i)` increases (not strictly) between `t'` and `t`
when `t' < t`. *)
lemma counterIncreaseBis:
  forall (t:timestamp), forall (t':timestamp), forall (i:index),
    happens(t) =>
      exec@t && t' < t =>
        (SCpt(i)@t' ~< SCpt(i)@t = orderOk || SCpt(i)@t = SCpt(i)@t').
(** This proof is done by induction, relying on the previous `counterIncrease`
lemma to prove the induction step. *)
Proof.
  induction.
  smt  ~steps:194607. 
Qed.

(** #### SECURITY PROPERTIES

We now state and prove the 3 following security properties:

* Property 1: absence of replay attacks.
* Property 2: injective correspondence.
* Property 3: monotonicity.

******************************************
*)

(**
#### Property 1: absence of replay attacks
This property states that the server never accepts for the same YubiKey the
same counter twice, _i.e._ if the trace is executable up until `S(ii1,i)`,
then there cannot exist a previous action `S(ii,i)` in the trace such that
`ii <> ii1` and `SCpt(i)@S(ii,i) = SCpt(i)@S(ii1,i)`.

Note that proving this property does not rely on any assumption on cryptographic
primitives: it relies only on reasonings about counter values.
*)

(**
We start by proving an invariant (`noreplayInv`) that will be useful in the
main proof.
This intermediate lemma states that whenever the server accepts for a given
YubiKey (represented by the index `i`), the counter value must have increased
compared to the last time the server accepted for this YubiKey.
*)
lemma noreplayInv (ii, ii1, i:index):
  happens(S(ii1,i),S(ii,i)) =>
  exec@S(ii1,i) && S(ii,i) < S(ii1,i) =>
  SCpt(i)@S(ii,i) ~< SCpt(i)@S(ii1,i) = orderOk.
(** The proof relies on the previous helping lemmas reasoning on counter
values. *)
Proof.
 use counterIncreaseBis; smt  ~steps:30438.
Qed.


lemma noreplay (ii, ii1, i:index):
  happens(S(ii1,i)) =>
    exec@S(ii1,i) && S(ii,i) <= S(ii1,i) && SCpt(i)@S(ii,i) = SCpt(i)@S(ii1,i) =>
      ii = ii1.
Proof.
  use noreplayInv; smt  ~steps:12186.
Qed.


(** #### Property 2: injective correspondence
This property states that a successful login for the YubiKey `pid(i)`
(_i.e._ the execution of action `S(ii,i)`) must have been preceded by
a button press on this YubiKey for the same counter value (`P(i,j)` with
`cpt(i,j)@Press(i,j) = SCpt(i)@S(ii,i)`), and this counter value is not
involved in another successful login.

Proving this property requires to reason on counter values, but also requires
the use of the INT-CTXT cryptographic assumption.
*)
lemma injective_correspondence (ii,i:index): 
  happens(S(ii,i)) =>
  exec@S(ii,i) =>
  exists (j:index),
    Press(i,j) < S(ii,i) && cpt i j@Press(i,j) = SCpt(i)@S(ii,i) && 
    forall (ii1:index), 
      happens(S(ii1,i)) => 
      exec@S(ii1,i) =>
      cpt i j@Press(i,j) = SCpt(i)@S(ii1,i) => 
      ii1 = ii.
(** The high-level idea of this proof is to use the INT-CTXT assumption:
if the message received by the server is a valid ciphertext, then it must
be equal to an encryption that took place before.

Since the action `Press(i,j)` is the only one that outputs an encryption,
we thus have the existence of such an action before in the trace.
Then, the unicity is proved using lemmas on counter values.
*)
Proof.
  intro Hap Hexec.
  rewrite /exec /cond in Hexec.
  destruct Hexec as [Hexecpred [Mneq Hcpt] Hpid].
  (** We apply the INT-CTXT assumption, which directly gives the existence
  of an action `Press(i,j)` that happens before `S(ii,i)`. *)
  intctxt Mneq => //.
  (** The two first conjucts of the conclusion are automatically proved
  by Squirrel (the equality of counter values is a consequence of M1 once
  we have expanded the macros `cpt` and `SCpt`. *)
  (** It now remains to show that the counter value `cpt(i,j)@Press(i,j)` is
  not involved in another successful login, and this is done automatically 
  relying on counterIncreaseBis and the smt tactic *)
  use counterIncreaseBis. smt ~steps:207165. 
Qed.



(** #### Property 3: monotonicity
This property states that the counter values associated to successful logins are
monotonically increasing in time.

Note that proving this property does not rely on any assumption on cryptographic
primitives: it relies only on reasonings about counter values.
*)
lemma monotonicity (ii, ii1, i:index):
  happens(S(ii1,i),S(ii,i)) =>
    exec@S(ii1,i) && exec@S(ii,i)
      && SCpt(i)@S(ii,i) ~< SCpt(i)@S(ii1,i) = orderOk =>
        S(ii,i) < S(ii1,i).
Proof.
 use noreplayInv; smt  ~steps:23195.
Qed.

