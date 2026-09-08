(* ------------------------------ *)
(* Modelisation of the protocol *)
(* This files propose a modelisation of the Signal assymetric ratchet,
   with a unique session between two agents.
   Some axioms are added to asume that the attacker is non-adaptative,
   meaning the moments the attacker may corrupt is determined before
   the execution. *)
include "indices.sp". 
include "DHLib.sp".
include Int.
open Int.

set processStrictLetMode=true.

(* ------------------------------ *)
(* Some axioms on pairs *)

(* TODO : remove this axioms with other type of hash functions? *)
axiom[any] proj_inj (x,y:message) : (fst x = fst y && snd x = snd y) => x = y.

(* We add an axiom on order that is not by default in Squirrel.
   This axiom is unsound on polymorphic type, since for timestamps `tau <= tau`
   implies `happens tau`.
   So we add this axiom only for the pair type `(index*bool)`, which is sound. *)
axiom[any] eq_impl_le (p : (index*bool)) : p <= p.

(* ------------------------------ *)
(* Declarations for the protocol *)

channel c.

(* For each agent, a set of steps, represented by their indices,
   are predetemined before the execution.
   At these steps, the attacker cannot corrupt the agent. *)
abstract safeR : index -> boolean.
abstract safeI : index -> boolean.
axiom[any] safeR_zero :
  safeR (ind_zero)  = true.
axiom[any] safeI_zero :
  safeI (ind_zero)  = true.

(* Keyed hash function and its key modelling the KDF used to derive
   a new root key from the previous one and a DH secret. *)
hash h
name k : message.
(* We assume the game PreImage Resistance on our hash function `h`:
   Given a value `goal`, the attacker cannot find a preimage `x`
   such that `h(x,k) = goal`.
   This assumption is a consequence of the PRF assumption. *)
game PIR = {
  rnd k:message;
  let goal : message = #init;
  oracle get_h x = { return h(x,k) }
  oracle get_goal = { return goal }
  oracle challenge x = { return diff(h(x,k) <> goal, true) }
}.

(* Keyed hash function and its key modelling the KDF used to derive
   a chain key from a root key. *)
hash h'
name k' : message.

(* Diffie-Hellman secrets at each step, used by agents `R` and `I` *)
abstract zE : E.
name skR : index -> E
name skI : index -> E

(* Type conversion from exponents to messages, to output corrupted
exponents to the attacker. *)

abstract ofE : E -> message.

(* Initial root key *)
name s_init : message

(* Each agent have two mutable states to register the root keys they
   derive at each steps.  Their initial values model the result of th
   X3DH key-exchange occuring before the assymetric ratchet, followed
   by the first half ratchet step on the initiator side..
   `RKRreceive` is not initialised, so we write a dummy secret value
   inside, used only to simplify the proof of induction which enables
   to prove secrecy over all values.*)

name s_dum : message
mutable RKRreceive : message = s_dum

mutable RKRsend : message = s_init
mutable RKIreceive : message = s_init
mutable RKIsend : message = h(<s_init, ofG((g^(skR ind_zero))^(skI ind_zero))>,k)

(* A state register what the attacker will learn if they corrupt now.
   During the `i`-th action of agent `R`, this state is put to `zero`
   if `safeR i` and `RKRsend@R i` otherwise.
   That way, the cannot cannot learn a value during safe steps, even
   if there is a corruption.*)
mutable stRCor : message = zero.
mutable stICor : message = zero.

mutex lR : 0.
mutex lI : 0.


(* ------------------------------ *)
(* Protocol *)

process Responder (i : index) = (* at the first execution, we must have `i = ind_one` *)
  lock lR;
  (* The agent input a DH public value `gI`. *)
  in(c, x);
  let gI = toG(x) in

  (* With `gI`, the agent compute two shared secrets.
     One with their previous secret, and one with the newly sampled secret. *)
  let gRecR =  gI^(skR (ind_pred i)) in
  let gSendR = gI^(skR i) in
  (* `pkR` is the public key for the next DH exchange. *)
  let pkR =  g^(skR i) in
  (* The agent perform two ratchet steps *)
  RKRreceive :=  h(<RKRsend, ofG(gRecR)>, k); 
  RKRsend := h(<RKRreceive, ofG(gSendR)>, k);
  (* `stRCor` register `RKRsend` only if a corruption is possible at this step,
     so if `safeR i` does not hold. *)
  stRCor := if safeR i then zero else <RKRsend, ofE(skR i)>;
  (* The agent output three elements:
     - Their DH public value,
     - Their receiving chain key, derived  from `RKRreceive`
     - Their sending chain key, derived from `RKRsend`.
     The last two model that we may have a fully compromise symmetric
     ratchet, and try to prove in this context the security of the
     asymmetric ratchet.

 *)
  out(c, <ofG(pkR), <h'(RKRreceive,k'), h' (RKRsend, k')>>);
  unlock lR.

(* The `Initiator` is similar to the `Responder` *)
process Initiator (i : index) =
  lock lI;
  in(c, y);
  let gR = toG(y) in
  let gRecI = gR^(skI (ind_pred i)) in
  let gSendI = gR^(skI i) in
  let pkI =  g^(skI i)  in
  RKIreceive := h(<RKIsend, ofG(gRecI)>, k);   (* h( ..., g^b i-1 a i ) *)
  RKIsend := h(<RKIreceive, ofG(gSendI)>, k);
  stICor := if safeI i then zero else <RKIsend, ofE(skI i)>;
  out(c, <ofG(pkI), <h' (RKIreceive,k'), h'(RKIsend,k')>> );
  unlock lI.

(* Expected executions:
   RKRsend@R i = RKIreceive@I i
   StRReceive@R i = RKIsend@I (i-1) *)

(* `Cor` try to leak both the sending root key of `R` and `I` when
   it is called.
   `stRCor` (resp. `stICor`) does not contain the root key if the
   previous `R` (resp. `I`) was safe.*)
process Corrupt (j : index) =
  out(c, <stRCor,stICor>).

(* The hash functions are keyed, so the attacker needs access to
   random oracle actions to compute hashes. *)
process RO (j : index) =
  in(c, m);
  out(c, h (m,k))

process RO' (j : index) =
  in(c, m);
  out(c, h'(m,k'))

system S = Izero: out(c, <ofG( g^(skR ind_zero)),
                          <ofG( g^(skI ind_zero)),
                           h'(RKIsend,k')>>);
  (* The action `Izero` models the message send during the X3DH
     initialisation along with the first DR half-step: `RKIsend` was
     initialized with `h(<s_init, ofG((g^(skR 0))^(b 0))>,k)`,
     assuming `g^skR 0` was alredy sent out over the network.  We also
     leak for the CKIsend key, to model a fully compromised symmetric
     ratchet.  *)

(
  (!_i R: Responder i) |
  (!_i I: Initiator i) |
  (!_j Cor: Corrupt j) |
  (!_j RO : RO  j) | 
  (!_j RO': RO' j)
).



(* ------------------------------ *)
(*        Rxioms on actions       *)

(* To simplify the proof, we number the action `R` and `I` according
   to their place in the trace, starting at 1, and follows the
   order `~<` on indices.
   We also suppose without loss of generality, that there are more
   indices than the one used in the trace, so for any action
   `R i` or `I i`, `i ~< ind_max`. *)

exact axiom initR @system:S (i : index) : happens(R i) => ind_zero ~< i.
hint smt initR.

exact axiom initI @system:S (i : index) : happens(I i) => ind_zero ~< i.
hint smt initI.

exact axiom maxR @system:S (i : index) : happens(R i) => i ~< ind_max.
hint smt maxR.

exact axiom maxI @system:S (i : index) : happens(I i) => i ~< ind_max.
hint smt maxI.

exact axiom orderR @system:S (i,j : index) :
happens(R j) => ind_zero ~< i => i ~< j => R i < R j.
hint smt orderR.

exact axiom orderI @system:S (i,j : index) :
happens(I j) => ind_zero ~< i => i ~< j => I i < I j.
hint smt orderI.

(* sanity check *)
lemma _ @system:S (i:index) :
ind_zero ~< i => happens(R (ind_succ i)) => happens(R i).
Proof.
  smt.
Qed.



(* -------------------------------- *)
(*   Sync and Healthy predicate def  *)

exact axiom [any] lt_lexico_carac (x,x' : index, y,y' : int): 
    (x,y) < (x',y') <=> x < x' || ( x = x' && y < y').
hint smt lt_lexico_carac.


(* We define the predicates which will capture whether R and I
"synced" together, i.e. are deriving the same root keys. It is
mutually recursive, depending on whether both parties derive the same
shared DH secret at every step, We will later prove that indeed, this
high-level predicate which only depends on the trace, does capture the
expected synchronization property.  *)

(* syncRI is meant to be equivalent to RKRsend@R i = stIRec@I i *)
let rec syncRI @system:S (i:index) =
  i = ind_zero ||
  (R i < I i &&
   syncIR (ind_pred i) &&
   gSendR@ R i = gRecI@ I i)
termination_by (i,1)
(* syncIR is meant to be equivalent to: RKIsend@I i = stRRec@R (i+1) *)
and syncIR i =
 ( i= ind_zero && gI@ R (ind_one) = g^(skI ind_zero))
||
  (I i < R (ind_succ i) &&
   syncRI i &&
   gRecR@ R (ind_succ i) = gSendI@ I i)
termination_by (i,2).
Proof. 
 split.
 + intro i Neg Ord.
   rewrite lt_lexico_carac. by right.
 + intro i Neq Ord.
   rewrite lt_lexico_carac. left. apply ind_to_leq. smt.
Qed.



(* We define the healthyX predicate, which will capture that the RKXsend is secret. 

A sending root key on the receiver side is secret only if:

 - we have safeR, which means this particular root key cannot be
   corrupted by the attacker.
 - we have either one of  the two inputs (StRRec@R i and g^{a i * b (i-1)}) 
   to the kdf which must be secret, and so it must either be that:L
    + (safeI && gI= g^{b (i - 1)})): this is the healing step, where
    we received the honest and expected DH public key, and this public
    key cannot be compromised due to safeI.

    + if it not a healing step, the healthyness depends on the
      previous root key. There are then two cases, where if we are
      synced, then the initiator is deriving the same key as us, the
      initiator must then itself be healthy and uncompromised. If we
      are not synced, the secrecy must come from the fact that we
      ourselves were healthy at the previous step.  
*)
let rec healthyR @system:S  (i:index) =
 i=ind_zero || 
  (safeR i &&
  ( (if  syncIR (ind_pred i)  then  healthyI (ind_pred i) else healthyR (ind_pred i))
      || 
   (safeI (ind_pred i) &&
    gI@R i = g^(skI (ind_pred i)))))
termination_by (i,1)
(* On the other side, the situation is mirrored. *)
and healthyI i =
  safeI i &&
  (( if syncRI i then healthyR i  else healthyI (ind_pred i))
   || 
   (safeR i &&
    gR@I i = g^(skR i))) 
termination_by (i,2).
Proof.
 repeat split.
 + intro i Ord.
   rewrite lt_lexico_carac. intro _.   have U : i <> ind_zero. smt.  left. apply ind_to_leq. smt.
 + intro i Ord _.
   rewrite lt_lexico_carac. by right.
 + intro i Neq Sf _.
   rewrite lt_lexico_carac. left. apply ind_to_leq. smt.
 + intro i Neq Sf _.
   rewrite lt_lexico_carac. left. apply ind_to_leq. smt.
Qed.

(* axiomatise that the recursively defined healthy and sync predicates
   are in fact equal to abstract (and thus det) predicates Healthy, Sync.
   i.e. the time points where healing and sync occur are fixed, rather
        than dynamically chosen. *)
abstract HealthyR : index -> bool.
abstract HealthyI : index -> bool.
abstract SyncRI : index -> bool.
abstract SyncIR : index -> bool.

exact axiom healthyR_to_HealthyR @system:S (i:index) :
   healthyR i = HealthyR i.

exact axiom healthyI_to_HealthyI @system:S (i:index) :
   healthyI i = HealthyI i.

exact axiom syncRI_to_SyncRI @system:S (i:index) :
   syncRI i = SyncRI i.

exact axiom syncIR_to_SyncIR @system:S (i:index) :
   syncIR i = SyncIR i.


