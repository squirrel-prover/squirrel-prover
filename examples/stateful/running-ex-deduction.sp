(*******************************************************************************
RUNNING EXAMPLE

This protocol is a variant of the OSK protocol described in:
M. Ohkubo, K. Suzuki, S. Kinoshita et al.,
“Cryptographic approach to “privacy-friendly” tags,”
RFID privacy workshop, vol. 82. Cambridge, USA, 2003.

Each tag is associated to a mutable state sT initialized with s0.
Readers have access to a database containing an entry sR for each authorized
tag.

         sT := H(sT,k)
T -> R : G(sT,k')

         input x; sR := H(sR,k) if x = G(H(sR,k),k') with sR in DB
R -> T : ok

COMMENTS
- In this model we add in parallel a process in order to provide the attacker
the ability to compute hashes with their respective keys (without knowing these
keys).
- The reader process is not modelled here, this is left for future work.

*******************************************************************************)

set autoIntro = false.

hash H
hash G
name k : message
name k' : message

name s0  : index -> message
name s0b : index -> message     (* renamed identities *)

mutable sT(i:index) : message = diff(s0(i),s0b(i))
mutable sR(i:index) : message = diff(s0(i),s0b(i))

abstract ok : message
channel cT
channel cR

process tag(i:index) =
  sT(i):=H(sT(i),k);
  out(cT,G(sT(i),k'))

process reader =
  in(cT,x);
  try find ii such that x = G(H(sR(ii),k),k') in
    sR(ii):=H(sR(ii),k);
    out(cR,ok)

system (!_i !_j T: tag(i) | !_jj R: reader).

set showStrengthenedHyp=true.

(* Assuming the secret keys and secret identities are indistinguishable,
   we prove that the state variables `sT` and `sR` are indistinguishable. *)
global goal deduce_state_ind (t : timestamp):
  [happens(t)] ->
  equiv(k, k', seq(i:index -> diff(s0(i),s0b(i)))) ->
  equiv(k, k', seq(i:index -> sT(i)@t), seq(i:index -> sR(i)@t)).
Proof.
  intro Hap H.

  (* a simple application of `H` fails, since proving that `sT` (resp. `sR`)
     can be bi-deduce from `H` require some form of inductive reasoning. *)
  checkfail apply H exn ApplyMatchFailure.

  (* with user input, we are able to do the proof, by induction over `tau` *)
  dependent induction t => t HI Hap.
  case t => Eq;
  repeat destruct Eq as [_ Eq].

  expandall.
  by apply H.

  expandall.
  by apply HI (pred(t)).

  expandall.
  by apply HI (pred(t)).

  expandall.
  by apply HI (pred(t)).
Qed.

(* Using our improvement of the bi-deduction checker with inductive
   reasoning, we can conclude directly without further user interaction.
   Note that timestamp t does not need to happen. *)
global goal deduce_state (t : timestamp):
  equiv(k, k', seq(i:index -> diff(s0(i),s0b(i)))) ->
  equiv(seq(i:index -> sT(i)@t), seq(i:index -> sR(i)@t)).
Proof.
  intro H.
  apply ~fadup H.
Qed.

(* We can even go further, and show that the value of the state variables
   `sT` and `sR` can be simultaneously deduced at all times. *)
global goal deduce_state_gen :
  equiv(k, k', seq(i:index -> diff(s0(i),s0b(i)))) ->
  equiv(
    seq(i:index, t':timestamp -> sT(i)@t'),
    seq(i:index, t':timestamp -> sR(i)@t')).
Proof.
  intro H.

  (* a simple application of `H` fails. *)
  checkfail apply H exn ApplyMatchFailure.

  (* using our improvement with inductive, we conclude directly *)
  apply ~fadup H.
Qed.
