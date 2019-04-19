module Imap : Map.S with type key = int

module type Ordered = sig
  type t
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end

(** Create a union-find data-structure over elements of type 'a.
    [union t u v] always uses the representent of [v], i.e.
    [find [union t u v] u] = [find t v] *)
module Uf (Ord: Ordered) : sig
  type v = Ord.t
  type t
  val create : v list -> t
  val find : t -> v  -> v
  val union : t -> v -> v -> t

  (** [classes t] return the list of equivalence classes of [t], where a class
      is represented by the list of its elements. *)
  val classes: t -> v list list

  val print : Format.formatter -> t -> unit
end
