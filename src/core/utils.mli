(** Utility modules. *)

module Hashtbl : sig
  include module type of Hashtbl

  val to_list : ('a, 'b) t -> ('a * 'b) list

  module Make2
      (H1:HashedType)
      (H2:HashedType) : S with type key = H1.t * H2.t
end

(*------------------------------------------------------------------*)
module List : sig
  include module type of List 

  (** [init n f] returns the list containing the results of
      [(f 0)],[(f 1)] ... [(f (n-1))].  *)
  val init : int -> (int -> 'a) -> 'a list

  val split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list

  (** [merge_uniq cmp l1 l2] behaves like [List.merge cmp l1 l2], except that
      it removes duplicates, w.r.t. [cmp], between [l1] and [l2].
      Duplicates already in [l1] or [l2] may remains. *)
  val merge_uniq : ('a -> 'a -> int) -> 'a list -> 'a list -> 'a list

  val remove_duplicate : ('a -> 'a -> bool) -> 'a list -> 'a list

  (** Removes from l all elements that are subsumed by another.
      [included x y] iff x included in y, ie y subsumes x. *)
  val clear_subsumed : ('a -> 'a -> bool) -> 'a list -> 'a list

  (** maps, splits, then flattens *)
  val flattensplitmap :
    ('a -> 'b list * 'c list) -> 'a list -> 'b list * 'c list

  (** Takes a list of n lists [a1;…;an], and assuming each ai has m elements,
      returns [b1;…;bm] where bi = [a1i;…;ani].
      Fails if all ai do not have the same length *)
  val megacombine : 'a list list -> 'a list list
     
  val inclusion : 'a list -> 'a list -> bool

  (** [diff a b] is [a] minus [b]'s elements  *)
  val diff : 'a list -> 'a list -> 'a list
 
  (** [take n l] returns up to the [n] first elements from list [l], if available. *)
  val take : int -> 'a list -> 'a list

  (** [drop n l] returns [l] without the first [n] elements, or the empty list 
      if [l] has less than n elements. *)
  val drop : int -> 'a list -> 'a list

  (** [drop_right n l] returns [l] without the last [n] elements, or the empty list 
      if [l] has less than n elements. *)
  val drop_right : int -> 'a list -> 'a list

  (** [takedrop n l] returns the a result equal to [take n l, drop n l]. *)
  val takedrop : int -> 'a list -> 'a list * 'a list

  (** When [0 <= i < List.length l], [splitat i l] returns [before,e,after]
      such that [List.rev_append before (e::after) = l] and
      [List.length before = i].
      @raise Out_of_range when [i] is out of range. *)
  val splitat : int -> 'a list -> 'a list * 'a * 'a list

  (** Update in an associative list *)
  val assoc_up : 'a -> ('b -> 'b) -> ('a * 'b) list -> ('a * 'b) list

  val assoc_up_dflt : 'a -> 'b -> ('b -> 'b) -> ('a * 'b) list -> ('a * 'b) list

  val assoc_dflt : 'b -> 'a -> ('a * 'b) list -> 'b

  val iteri2 : (int -> 'a -> 'b -> unit) -> 'a list -> 'b list -> unit

  val last : ?e:exn -> 'a list -> 'a

  val map_fold  : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
  
  val mapi_fold : (int -> 'a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list

  val foldi : (int -> 'a -> 'b -> 'a) -> 'a -> 'b list -> 'a

  val find_mapi : (int -> 'a -> 'b option) -> 'a list -> 'b option 

  val mem_cmp : eq:('a -> 'a -> bool) -> 'a -> 'a list -> bool

  exception Out_of_range
end

(*------------------------------------------------------------------*)
module String : sig
    include module type of String 

    val split_on_integer : string -> string * int option
  end

(*------------------------------------------------------------------*)
module Map : sig
  include module type of Map 

  module type S = sig
    include Map.S

    val add_list : (key * 'a) list -> 'a t -> 'a t 
    val find_dflt : 'a -> key -> 'a t -> 'a
  end

  module Make(O : Map.OrderedType) : S with type key = O.t
end


module Set : sig 
  include module type of Set 

  module type S = sig
    include Set.S

    val add_list : elt list -> t -> t 
    val map_fold : ('a -> elt -> 'a * elt) -> 'a -> t -> 'a * t
  end

  module Make(O : Set.OrderedType) : S with type elt = O.t
end

(*------------------------------------------------------------------*)
module Mi : Map.S with type key = int
module Si : Set.S with type elt = int

module Ms : Map.S with type key = string
module Ss : Set.S with type elt = string

(*------------------------------------------------------------------*)
module type Ordered = sig
  type t
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end

(*------------------------------------------------------------------*)
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
    [find \[union t u v\] u] = [find t v] *)
  val union : t -> v -> v -> t

  (** [classes t] return the list of equivalence classes of [t], where a class
      is represented by the list of its elements. 
      Remark: uses memoisation. *)
  val classes: t -> v list list

  val print : Format.formatter -> t -> unit

  (** [union_count t] is the number of non-trivial unions done building [t]. *)
  val union_count : t -> int

  (** For further memoisation. *)
  module Memo : Ephemeron.S with type key = t

  (** For further memoisation. *)
  module Memo2 (H2 : Hashtbl.HashedType) : Ephemeron.S 
    with type key = (t * H2.t)
end

(*------------------------------------------------------------------*)
(** [fpt comp f x] iters [f] untils it reachs a value [y] such that 
    [comp (f y) y] holds (in which case it returns [f y]). 
    - if [comp] is a reflexive relation, computes a fix-point of [f]. 
    - if [f] is monotonic w.r.t. [comp], computes a post-fixpoint of [f]. *)
val fpt : ('a -> 'a -> bool) -> ('a -> 'a) -> 'a -> 'a

(*------------------------------------------------------------------*)
(* Option type functions *)

val some : 'a -> 'a option

val oget      : 'a option -> 'a
val odflt     : 'a -> 'a option -> 'a
val obind     : ('a -> 'b option) -> 'a option -> 'b option
val omap      : ('a -> 'b) -> 'a option -> 'b option
val omap_dflt : 'b -> ('a -> 'b) -> 'a option -> 'b
val oiter     : ('a -> unit) -> 'a option -> unit
val oequal    : ('a -> 'b -> bool) -> 'a option -> 'b option -> bool

(*------------------------------------------------------------------*)
(** [classes f_eq l] returns the equivalence classes of [l] modulo [f_eq],
    assuming [f_eq] is an equivalence relation. *)
val classes : ('a -> 'a -> bool) -> 'a list -> 'a list list

(*------------------------------------------------------------------*)
val ident : Format.formatter -> string -> unit
val kw : Fmt.style -> string Fmt.t
val pp_ne_list :
  ('a -> 'b list -> unit, Format.formatter, unit) format ->
  'a -> Format.formatter -> 'b list -> unit
val pp_list :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a list -> unit

(*------------------------------------------------------------------*)
val fst3 : 'a * 'b * 'c -> 'a

(*------------------------------------------------------------------*)
(** [timeout exn t f x] executes [f x] for at most [t] seconds.
    Returns [f x] if the computation terminated in the imparted
    time, and [exn] otherwise. *)
val timeout : exn -> int -> ('a -> 'b) -> 'a -> 'b 

(*------------------------------------------------------------------*)
val fst_map : ('a -> 'c) -> 'a * 'b -> 'c
val snd_map : ('b -> 'c) -> 'a * 'b -> 'c

val fst_bind : ('a -> 'c) -> 'a * 'b -> 'c * 'b
val snd_bind : ('b -> 'c) -> 'a * 'b -> 'a * 'c

(*------------------------------------------------------------------*)
(** composition *)
val (-|) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b

(** inverse arguments *)
val (^~) : ('a -> 'b -> 'c) -> ('b -> 'a -> 'c)
  
(*------------------------------------------------------------------*)
val as_seq0 : 'a list -> unit
val as_seq1 : 'a list -> 'a
val as_seq2 : 'a list -> 'a * 'a
val as_seq3 : 'a list -> 'a * 'a * 'a
val as_seq4 : 'a list -> 'a * 'a * 'a * 'a

(*------------------------------------------------------------------*)
(** {2 Hash} *)

val hcombine : int -> int -> int
val hcombine_list : ('a -> int) -> int -> 'a list -> int                         

(*------------------------------------------------------------------*)
(** {2 Printing} *)

type assoc  = [`Left | `Right | `NonAssoc]
type fixity = [`Prefix | `Postfix | `Infix of assoc | `NonAssoc | `NoParens]

(* -------------------------------------------------------------------- *)
val pp_maybe_paren : bool -> 'a Fmt.t -> 'a Fmt.t 

val maybe_paren :
  inner:'a * fixity ->
  outer:'a * fixity ->
  side:assoc ->
  'b Fmt.t -> 
  'b Fmt.t

(*------------------------------------------------------------------*)
module Lazy : sig
  include module type of Lazy
      
  val map : ('a -> 'b) -> 'a t -> 'b t
end
