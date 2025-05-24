(** This module define the translation of a process into a system and
    its actions. *)

type lsymb = Symbols.lsymb
  
(*------------------------------------------------------------------*)
(** Final declaration of the system under consideration,
    which triggers the computation of its internal representation
    as a set of actions. *)
val declare_system :
  Symbols.table -> Action.exec_model -> lsymb option ->
  Projection.t list -> Process.Parse.t -> Symbols.table

(*------------------------------------------------------------------*)
(** Testing utility that corresponds to the first steps of [declare_system]
    but stops after the conflict analysis, prior to translation.
    It returns a hash table containing conflicts. *)
val system_conflicts :
  Symbols.table -> Projection.t list -> Process.Parse.t -> (int,int) Hashtbl.t
