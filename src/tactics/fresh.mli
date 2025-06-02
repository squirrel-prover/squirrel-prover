(** Tactics exploiting a name's freshness. *)
open Squirrelcore

module ES = EquivSequent


(** For a term [n] and terms [biframe], computes a list of formulas
    whose conjunction expresses that [n] is fresh in [biframe] and
    [n.args], after projecting on both projections of the system.  *)
    
val phi_fresh_pair :
  use_path_cond:bool ->
  ?loc:Location.t ->
  ES.sequent ->
  Term.term ->
  Term.terms ->
  Term.terms
