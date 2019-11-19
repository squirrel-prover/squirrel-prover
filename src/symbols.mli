(** A ['a t] is a globally declared symbol associated to a value
  * of type ['a]. *)
type 'a t

(** Convert a symbol to a string, for printing purposes. *)
val to_string : 'a t -> string

module type S = sig
  type t
end

(* Create a new kind of declaration in the global namespace,
 * where symbols are attached with the type [M.t]. *)
module Make (M:S) : sig

  (** Reserve a fresh symbol name, resembling the given string. *)
  val reserve : string -> M.t t

  (** Define a symbol name that has been previously reserved
    * using [fresh]. *)
  val define : M.t t -> M.t -> unit

  (** Declare a new symbol, with a name resembling the given string,
    * defined by the given value. *)
  val declare : string -> M.t -> M.t t

  (** Get the definition of a symbol in this namespace,
    * raise [Not_found] if it is not defined. *)
  val find : string -> M.t

end
