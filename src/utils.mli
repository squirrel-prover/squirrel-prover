module Imap : Map.S with type key = int

module type OrderedType = Map.OrderedType

(** Create a union-find data-structure over elements of type 'a.
    [union t u v] always uses the representent of [v], i.e.
    [find [union t u v] u] = [find t v] *)
module Uf (Ord: OrderedType) : sig
  type v = Ord.t
  type t
  val create : v list -> t
  val find : t -> v  -> v
  val union : t -> v -> v -> t

end
