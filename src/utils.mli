module List : sig
  include module type of struct include List end

  (** [init n f] returns the list containing the results of
      [(f 0)],[(f 1)] ... [(f (n-1))].  *)
  val init : int -> (int -> 'a) -> 'a list

  val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list

  (** [merge_uniq cmp l1 l2] behaves like [List.merge cmp l1 l2], except that
      it removes duplicates, w.r.t. [cmp], between [l1] and [l2].
      Duplicates already in [l1] or [l2] may remains. *)
  val merge_uniq : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

  (** [split_pred f l] split [l] into the list of elements where [f] holds and
      the list of elements where [f] does not hold, while respecting the
      ordering in [l]. *)
  val split_pred : ('a -> bool) -> 'a list -> 'a list * 'a list
end

module Imap : Map.S with type key = int

module type Ordered = sig
  type t
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end

(** Create a union-find data-structure over elements of type 'a.
    - [union] and [find] must only be used on elements present at the
    creation, or on elements added afterwards through [extend]. *)
module Uf (Ord: Ordered) : sig
  type v = Ord.t
  type t

  val create : v list -> t

  (** [extend t v] add the element [v] to [t], if necessary. *)
  val extend : t -> v -> t

  val find : t -> v  -> v

  (** [union t u v] always uses the representent of [v], i.e.
    [find [union t u v] u] = [find t v] *)
  val union : t -> v -> v -> t

  (** [classes t] return the list of equivalence classes of [t], where a class
      is represented by the list of its elements. *)
  val classes: t -> v list list

  val print : Format.formatter -> t -> unit

  (** [union_count t] is the number of non-trivial unions done building [t] *)
  val union_count : t -> int
end

val fpt : ('a -> 'a) -> 'a -> 'a

(* Option type functions *)
val opt_get : 'a option -> 'a
val some : 'a -> 'a option
val opt_map : 'a option -> ('a -> 'b option) -> 'b option

(** [classes f_eq l] returns the equivalence classes of [l] modulo [f_eq],
    assuming [f_eq] is an equivalence relation. *)
val classes : ('a -> 'a -> bool) -> 'a list -> 'a list list
