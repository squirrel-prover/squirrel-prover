(*******************************************************************************
# Hash-Lock: Authentication

Hash-Lock is an authentication protocol played between a RFID tag
`T(i)` (where `i` is the identity of the tag) and a RFID reader
R. The goal of the protocol is to provide authentication of the tag to
the reader, while preserving the tag's privacy.

The protocol proceeds as follows:

  R    --> T(i) : nR
  T(i) --> R    : < nT, h(<nR, nT>, kT(i)) >
  R    --> T(i) : ok

Reference:
- Ari Juels and Stephen A. Weis. Defining strong privacy for RFID. ACM
  Trans. Inf. Syst. Secur., 13(1):7:1–7:23, 2009.

*******************************************************************************)

include Basic.

(* ----------------------------------------------------------------- *)
(** ## declarations *)

hash h

abstract ok : message
abstract ko : message

(* `key(i)` is the key of the tag `i` *)
name key : index -> message

(* channel for tag messages *)
channel cT

(* channel for reader messages *)
channel cR

(* ----------------------------------------------------------------- *)
(** ## processes *)

(* session number `k` of the RFID tag with identity `i` *)
process tag(i:index,k:index) =
  new nT;
  in(cR,nR);
  T: out(cT, < nT,h(<nR, nT>, key(i)) >)

(* session number `j` of the reader R *)
process reader(j:index) =
  new nR;
  R: out(cR,nR);
  in(cT,x);
  if exists (i:index), snd(x) = h(<nR, fst(x)>, key(i)) then
    R1: out(cR,ok)
  else
    R2: out(cR,ko)

system (
  (!_j     R: reader(j) ) |     (* single reader, many sessions *)
  (!_i !_k T: tag(i,k)  )       (* many tags, many session *)
).

(* ----------------------------------------------------------------- *)
(** ## preliminaries: macros and protocols *)

(* The term `output@R1(j)`, called a macro, represents the output of
   the session `j` of the reader for the action `R1`, *if* the action
   `R1(j)` did occur in the protocol execution (which is captured by
   the predicate `happens(R1(j))`). *)
goal macro_0 (j : index) : 
  happens(R1(j)) =>
  output@R1(j) = ok.
Proof.
  intro Hap.
  (* clear Hap. *) 
 
  (* If the timestamp `t` occurs, the macro `m@t` can be expanded into 
     its definition using the rewrite tactic: `rewrite /m`. 

     For example, for the `output` macro: *)
  rewrite /output.
  apply eq_refl.
Qed.
  (* Note that it is necessary that `R1(j)` happens, or the macro expansion 
     will fail. 
     You can test it by removing the `Hap` hypothesis: simply 
     un-comment the `clear Hap` tactic in the proof script above. *)


(* In the reader process, we see that the action `R1(j)` always 
   occur after the action `R(j)`.
   Such execution dependencies can be exploited by the `depends` tactic. *)
goal macro_1 (j : index) : 
  happens(R1(j)) => happens(R(j)).
Proof.
  intro Hap.
  by depends R(j), R1(j).
Qed.

(* Prove the following lemma *without* relying on `auto`.
   Hint: first prove that `R(j)` happens with `have`. *)
goal macro_2 (j : index) : 
  happens(R1(j)) =>
  output@R(j) = nR(j).
Proof.
  admit. (* TODO *)
Qed. 

(* ----------------------------------------------------------------- *)
(** ## security proofs *)

(* First, we prove that if the session `k` of the tag `i` (which is `T(i,j)`) 
   inputs the name `nR(j)`

     `input@T(i,k) = nR(j)`

   then the session `j` of the reader `R(j)` must have started before the tag

     `R(j) < T(i,k)`   
*)
goal fresh_nR (i, j, k : index) :
  happens(T(i,k)) =>
  input@T(i,k) = nR(j) =>
  R(j) < T(i,k).
Proof.
  admit. (* TODO *)
Qed.

(* Well-authentication for `R1(j)`. We show that 

   (1) the session `j` of the reader ends by accepting the tag
       with identity `i` 
   
   if and only if

   (2) there exists a session `k` of the tag `i` such that
     - session `k` of tag `i` started after session `j` or the reader started: 
          `R(j) < T(i,k)`
     - session `k` of tag `i` started before session `j` of the reader ended: 
         `T(i,k) < R1(j)` 
     - the tag output has been correctly forwarded to the reader 
       (component by component): 
         `fst(output@T(i,k)) = fst(input@R1(j))`
         `snd(output@T(i,k)) = snd(input@R1(j))`
     - the initial reader output has been correctly forwarded to the tag: 
         `input@T(i,k) = output@R(j))` 
*)
goal wa_R1 (j:index):
  happens(R1(j)) =>
  cond@R1(j)
  <=>
  (exists (i,k:index), 
    R(j) < T(i,k) && T(i,k) < R1(j) &&
    fst(output@T(i,k)) = fst(input@R1(j)) &&
    snd(output@T(i,k)) = snd(input@R1(j)) &&
    input@T(i,k) = output@R(j)).
Proof. 
  admit. (* TODO *)
Qed.

(*-------------------------------------------------------------------*)
(* Injective authentication property. 
   QUESTION 1: 
     Before proving the `injective_auth` lemma, explain what it 
     intuitively means. 

   QUESTION 2: 
     Prove the `injective_auth` lemma below (difficulty: medium).

   QUESTION 3:
     Does the Basic-Hash protocol seen in the slides satisfy this property? *)
goal injective_auth (j:index):
  happens(R1(j)) =>
  cond@R1(j) =>
    (exists (i,k:index),
      R(j) < T(i,k) && T(i,k) < R1(j) &&
      fst(output@T(i,k)) = fst(input@R1(j)) &&
      snd(output@T(i,k)) = snd(input@R1(j)) &&
      input@T(i,k) = output@R(j) &&
      (forall (j0:index),
         happens(R1(j0)) =>
         cond@R1(j0) =>
         fst(output@T(i,k)) = fst(input@R1(j0)) =>
         snd(output@T(i,k)) = snd(input@R1(j0)) =>
         j = j0
      )
    ).
Proof.
  admit. (* TODO *)
Qed.
