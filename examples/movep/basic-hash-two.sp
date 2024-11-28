(*
   BASIC HASH

   The Basic Hash protocol as described in [Brusò et al., 2010]
   is an RFID protocol involving:

   - a tag associated to a secret key;
   - generic readers having access to a database containing all these keys.

   The protocol is as follows:

   T --> R : <nT, h(nT,kT)>
   R --> T : ok

   kT is the key of T, stored in the readers' database.
   nT is a session nonce.

   This file is an introductory example. It does NOT correspond to
   how we would normally model Basic Hash in Squirrel. Proof scripts
   use a minimum of ingredients and are thus unnecessarily tedious.
*)

(* Declare a hash function h that satisfies PRF, hence EUF. *)
include Core.

hash h.

(* Keys for tags T1 and T2. *)
name k1 : message.
name k2 : message.

(* Session nonces *)
name nt  : message.
name nt' : message.

(*dummy nones for the proof*)
name n1 : message.
name n2 : message.

(* Pseudo-random function game *)

game PRF = {
  rnd key : message;
  var lhash = empty_set;
  var lchal = empty_set;

  oracle ohash x = {
    lhash := add x lhash;
    return if mem x lchal then zero else h(x,key) 
  }

  oracle challenge x = {
    rnd r : message;
   (* the list before update *)
    var old_lchal = lchal;
    lchal := add x lchal;

    return if mem x old_lchal || mem x lhash  then zero else diff(r, h(x,key))
  }
}.

print PRF.




(* Please ignore the next lines... *)
system null.

(* Declaring a goal phi as done next means that we are
   going to prove (phi ~ true). Logical connectives in phi
   are thus the dotted connectives, i.e. function symbols
   representing boolean operations. *)
lemma authentication :
  (* Assume tag T1 has run a session with nonce nt,
     and T2 with nonce nt'. *)
  (
    (* if reader accepts att(..) *)
    snd(att(<<nt,h(nt,k1)>,<nt',h(nt',k2)>>))
    = h(fst(att(<<nt,h(nt,k1)>,<nt',h(nt',k2)>>)),k1)
    ||
    snd(att(<<nt,h(nt,k1)>,<nt',h(nt',k2)>>))
    = h(fst(att(<<nt,h(nt,k1)>,<nt',h(nt',k2)>>)),k2)
  ) => (
    (* then att(..) is an honest input *)
    (fst(att(<<nt,h(nt,k1)>,<nt',h(nt',k2)>>)) = nt &&
     snd(att(<<nt,h(nt,k1)>,<nt',h(nt',k2)>>)) = h(nt,k1))
    ||
    (fst(att(<<nt,h(nt,k1)>,<nt',h(nt',k2)>>)) = nt' &&
     snd(att(<<nt,h(nt,k1)>,<nt',h(nt',k2)>>)) = h(nt',k2))
  ).
Proof.
  intro H. (* the inference ---- is like a local-formula implication *)
  case H.
  (* Reader recognizes valid input from T1. *)
  + euf H. intro Heuf. left. auto.
  (* Reader recognizes valid input from T2. *)
  + euf H. intro Heuf. right. auto.
  
Qed.

(* To prove an equivalence we use a global goal.
   The two sides of the equivalence are given at once,
   using diff(_,_) when the left and right sides differ. *)
global goal privacy :
  equiv(<nt,h(nt,k1)>,
        diff(<nt',h(nt',k1)>,
             <nt',h(nt',k2)>)).


Proof.
  (* First break the pairs. *)
  fa 0.
  fa 2.

  trans 3 : n1 ;1: sym; trans 3: n2.
  (* Apply transitivity, replacing hashes by dummy. *)
  + by fresh 3.
  + by crypto PRF .
  + by crypto PRF (key : k2).
Qed.
