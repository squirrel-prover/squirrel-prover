(** Tactics functions used for both trace and equivalence tactics. *)

(** [constraints s] proves the sequent using its trace formulas. *)
val constraints : TraceSequent.t -> bool Utils.timeout_r
