(* tests that system pairs are correctly renamed and projected when changing 
   systems context. *)

system [real]  null.
system [ideal] null.

(* --------------------------------------------------------------------------*)
name a : message.
name b : message.

global theorem [real/left, ideal/left] real_ideal (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau,diff(a,b)).
Proof. admit. Qed.

global theorem [ideal] strong_sec (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau,diff(a,b)).
Proof. admit. Qed.

global theorem
  [set: real/left, ideal/left; equiv: ideal/right, real/right]
  ideal_real (tau:timestamp[const])
  :
  [happens(tau)] ->
  equiv(frame@tau,diff(a,b)).
Proof. admit. Qed.

(* --------------------------------------------------------------------------*)
global theorem [set: real/left; equiv: real] _ (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau).
Proof.
  intro Hap.
  trans [ideal/left,ideal/right].
  * have A := real_ideal.  
    by apply A. 
  * by apply strong_sec.
  * by apply ideal_real.
Qed.

(* --------------------------------------------------------------------------*)
global theorem [set: real/left; equiv: real] _ (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau).
Proof.
  intro Hap.
  trans [ideal/left,ideal/right].
  * by apply real_ideal. 
  * by apply strong_sec.
  * by apply ideal_real.
Qed.
