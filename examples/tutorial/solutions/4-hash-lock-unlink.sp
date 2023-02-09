(*******************************************************************************
# Hash-Lock: Unlinkability

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

(* `key(i)` is the key of the tag `i` in the MANY-session scenario *)
name key : index -> message

(* `keyS(i,k)` is the key of the tag `i,k` in the SINGLE-session scenario *)
name keyS : index * index -> message

(* channel for tag messages *)
channel cT

(* channel for reader messages *)
channel cR

(* ----------------------------------------------------------------- *)
(** ## processes *)

(* - MANY-session scenario: session number `k` of the RFID tag 
     with identity `i` 

   - SINGLE-session scenario: single session if the RFID tag 
     with identity `i, k` *)
process tag(i:index,k:index) =
  new nT;
  in(cR,nR);
  T: out(cT, < nT,h(<nR, nT>, diff(key(i), keyS(i,k))) >)

(* session number `j` of the reader R *)
process reader(j:index) =
  new nR;
  R: out(cR,nR);
  in(cT,x);
  if exists (i, k:index), snd(x) = h(<nR, fst(x)>, diff(key(i), keyS(i,k))) then
    R1: out(cR,ok)
  else
    R2: out(cR,ko)

system (
  (!_j     R: reader(j) ) |     (* single reader, many sessions *)
  (!_i !_k T: tag(i,k)  )     
   (* - left, MANY-session scenario: 
           many tags, each tag plays many sessions
      - right, SINGLE session scenario: 
           many tags, each tag plays a single session 
   *)
).

(* ----------------------------------------------------------------- *)
(** ## preliminary: project *)

(* The system defined above actually defines two protocols: 
   - a left protocol `[default/left]` for the MANY-session scenario 
   - a right protocol `[default/right]` for the SINGLE-session scenario 

   Therefore, a reachability property over this system actually state that
   the property holds for *both* systems. *)

(* Sometimes, we do not need to make a distinction between the left and 
   right system. For example the first output of the reader is always
   `nR(j)`, in both the MANY-session and SINGLE-session scenarios. *)
goal project_0 (j : index) :
  happens(R(j)) =>
  output@R(j) = nR(j).
Proof. 
  auto. 
Qed.

(* At other times, the left and right protocols behaviors may differ, 
   which we can express using the `diff` operator in terms:
   `diff(t1,t2)` is a bi-term representing the term `t1` for the 
   left protocol and `t2` for the right protocol.

   For example, the tag does not use the same hash key in the 
   MANY-session and SINGLE-session scenario. *)
goal project_1 (i, k : index) :
  happens(T(i,k)) =>
  output@T(i,k) = 
  diff(< nT(i,k), h(<input@T(i,k), nT(i,k)>, key (i  )) >,
       < nT(i,k), h(<input@T(i,k), nT(i,k)>, keyS(i,k)) >).
Proof.
  intro Hap.
  (* To prove this, we can project the goal over its two sub-systems 
     using the `project` tactic. *)
  project. 
  - rewrite /output. 
    apply eq_refl.
  - rewrite /output. 
    apply eq_refl.
Qed. 

(* As an exercise, show that a reader action `R1(j)` starting before 
   a tag action `T(i,k)` cannot receive the tag randomness `nT(i,k)`
   (as it has not yet been sampled).
   
   Note: the `diff` operator below is obviously spurious, and only here 
         for the sake of the exercise.  *)
goal project_2 (i, k : index) :
  happens(T(i,k)) =>
  forall (j : index),
    R1(j) < T(i,k) =>
    diff(nT(i,k), nT(i,k)) <> 
    fst(input@R1(j)).
Proof.
  (* BEGIN EXO *)
  intro Hap.
  intro j H Eq. 
  by project; fresh Eq.
  (* END EXO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## authentication lemma, useful for the unlinkability proof *)

(* Well-authentication for both `R1(j)` and `R2(j)`. 
   This goal is similar to the goal in file `2-hash-lock-auth.sp`, except 
   that it applies to both  `R1(j)` and `R2(j)`, and to both the 
   MANY-session and SINGLE-session scenarios. 
   We admit it (the proof is very similar to the proof in the previous file). *)
goal wa_R1_R2 (tau:timestamp,j:index):
  happens(tau,R(j)) =>
  (exists (i,k:index),
     snd(input@tau) = h(<nR(j),fst(input@tau)>,diff(key(i),keyS(i,k))))
  <=>
  (exists (i,k:index),
     T(i,k) < tau && R(j) < T(i,k) &&
     fst(output@T(i,k)) = fst(input@tau) &&
     snd(output@T(i,k)) = snd(input@tau) &&
     input@T(i,k) = output@R(j)).
Proof.
  (* BEGIN EXO *)
  intro Hap.
  split.

  (* COND => WA *)
  + intro [i k H].
    project.

    (* LEFT *)
    - euf H. intro [k0 [_ _]].
      have Meq1: input@T(i,k0)=nR(j) by auto.
      exists i,k0 => /=.
      fresh Meq1 => // ?.
      * by depends R(j),R1(j).
      * by depends R(j),R2(j). 

    (* RIGHT *)
    - euf H. intro [_ _].
      have Meq1: input@T(i,k)=nR(j) by auto.
      exists i,k => /=.
      fresh Meq1 => // ?.
      * by depends R(j),R1(j).
      * by depends R(j),R2(j).

  (* WA => COND *)
  + by intro [i k _]; exists i,k.
  (* END EXO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## unlinkability proof *)

(* The SINGLE-session and MANY-session scenarios are indinstinguishable. 

   Recall that the `fadup` tactic can be useful to simplify 
   equivalence goals (syntax: `fadup i` where `i` is an integer indicating 
   the frame element you want to get rid of). *)
global goal unlinkability (t : timestamp[param]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  (* BEGIN EXO *)
  intro Hap. 
  induction t.

  (* init *)
  + auto.

  (* Case R *)
  + expand frame, exec, cond, output.
    fa !<_,_>; fa 1.
    fresh 1.
    repeat split => j0 _ //.
    by depends R(j0), R1(j0).
    by depends R(j0), R2(j0).
    auto.

  (* Case R1 *)
  + expand frame, exec, output.
    fa !<_,_>.
    rewrite /cond wa_R1_R2; 1: by depends R(j), R1(j).
    by fadup 1.

  (* Case R2 *)
  + expand frame, exec, output.
    fa !<_,_>.
    rewrite /cond wa_R1_R2; 1: by depends R(j),R2(j).
    by fadup 1.

  (* Case T *)
  + expand frame, exec, cond, output.
    fa !<_,_>; fa 1; fa !<_,_>.
    prf 2.
    rewrite if_true /=. {
      project;
      repeat split => > _ _ [_ Meq0]; (try fresh Meq0); auto.
    }
    fresh 2; 1:auto.
    by fresh 1.
  (* END EXO *)
Qed.
