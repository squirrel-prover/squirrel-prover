(** Basic module for variables, used to instantiate timestamp, index and
    messages variables *)

(** A variable type depends on an identifier counter, and on a default name *)
module type VarParam = sig
  val default_string : string
end

(** Module for a specific variable type *)
module type VarType = sig
  type t

  val reset_id_names : unit -> unit

(** [make_fresh ?name] creates a fresh variable, whose name is either based on
    the default name, or on [?name], concatenated with an integer to identify
    the variable. There is a counter for each name, which can be reset with
    [reset_id_names]. *)
  val make_fresh : ?name:string -> unit -> t

(** [get_or_make_fresh l n] returns either the first variable with name [n]
    inside the list [l] or returns a fresh variable, with name exactly the given
    name. Using this to create fresh variables may create parsing confusions,
    as multiple variables with the same name can be defined. *)
  val get_or_make_fresh : t list -> string -> t

  (** [name t] extracts the name of a variable *)
  val name : t -> string

  val pp : Format.formatter -> t -> unit
  val pp_list : Format.formatter -> t list -> unit
end

module Var(V:VarParam) : VarType

module Tvar : VarType

module Mvar : VarType

module Index : VarType

val reset_id_names : unit -> unit
