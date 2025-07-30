(** Tactics exploiting a name's freshness. *)
open Squirrelcore

module ES = EquivSequent


(** For a applied name [n args] and terms [biframe], computes a list
    of formulas whose conjunction expresses that [n] is fresh in
    [biframe] and [args], where all terms are taken in the system pair
    of the sequent. *)
val phi_fresh_pair :
  use_path_cond:bool ->
  ?loc:Location.t ->
  ES.sequent ->
  Term.term ->
  Term.terms ->
  Term.terms
