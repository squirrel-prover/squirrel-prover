(** Basic module for variables, usde to instantiate timestamp, index and
    messages variables *)

(** A variable type depends on an identifier counter, and on a default name *)
module type VarParam = sig
  val default_string : string
  val cpt : int ref
end

(** Module for a specific variable type *)
module type VarType = sig
  type t

(** [make_fresh ?name] creates a fresh variable, whose name is either based on
    the default name, or on [?name]*)
  val make_fresh : ?name:string -> unit -> t

(** [get_or_make_fresh l n] returns either the first variable with name [n]
    inside the list [l] or returns a fresh variable. *)
  val get_or_make_fresh : t list -> string -> t

  (** [name t] extracts the name of a variable *)
  val name : t -> string

  val pp : Format.formatter -> t -> unit
  val pp_list : Format.formatter -> t list -> unit
end

module Var(V:VarParam) : VarType
