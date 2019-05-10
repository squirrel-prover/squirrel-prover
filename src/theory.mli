(** Terms may represent indices, messages or booleans *)

type kind = Index | Message | Boolean

(** Declaration of new function symbols, names and mutable cells
  *
  * Hash function symbols are of kind message->message->message.
  * Asymmetric encryption function symbols are of kind
  * message->message->message->message.
  * Names and mutables are of kind index^n->message. *)

val declare_hash : string -> unit
val declare_aenc : string -> unit
(* TODO move here
 * val declare_name : string -> int -> unit
 * val declare_mutable : string -> int -> unit *)

(** Terms *)

type ord = Eq | Neq | Leq | Geq | Lt | Gt

type term =
  | Var of string
  | Name of string * term list
  | Get  of string * term list
      (** [Get (s,terms)] reads the contents of memory cell
        * [(s,terms)] where [terms] are evaluated as indices. *)
  | Fun  of string * term list
      (** Function symbol application,
        * where terms will be evaluated as indices or messages
        * depending on the type of the function symbol. *)
  | Compare of ord*term*term

(** Facts *)

type fact = term Term.bformula

(** Declaration of macros *)

type arg_spec = (string*kind) list

val declare_term : string -> arg_spec -> term -> unit

(** Term builders *)

val make_term : string -> term list -> term
val make_pair : term -> term -> term
