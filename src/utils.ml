module Imap = Map.Make (struct
  type t = int
  let compare = Pervasives.compare
end)

module type OrderedType = Map.OrderedType

(** Create a union-find data-structure over elements of type 'a. *)
module Uf (Ord: OrderedType) : sig
  type v = Ord.t
  type t
  val create : v list -> t
  val find : t -> v  -> v
  val union : t -> v -> v -> t

end = struct

  type v = Ord.t
  module Vmap = Map.Make(Ord)
  (* rmap is the inverse of map *)
  type t = { map : int Vmap.t;
             rmap : v Imap.t;
             puf : Puf.t }

  let create l =
    let _,m,rm =
      List.fold_left (fun ( i, m, rm ) a ->
          ( i+1, Vmap.add a i m, Imap.add i a rm ))
        ( 0, Vmap.empty, Imap.empty ) l in

    { map = m;
      rmap = rm;
      puf = Puf.create (List.length l) }

  let find t u =
    let ru_eqc = Vmap.find u t.map |> Puf.find t.puf in
    Imap.find ru_eqc t.rmap

  let swap t u u' =
    let i = Vmap.find u t.map
    and i' = Vmap.find u' t.map in

    { t with map = Vmap.add u i' t.map
                   |> Vmap.add u' i;
             rmap = Imap.add i u' t.rmap
                    |> Imap.add i' u }

  let union t u u' =
    let i' = Vmap.find u' t.map in

    let t' = { t with puf = Puf.union t.puf
                          (Vmap.find u t.map)
                          (Vmap.find u' t.map) } in

    if i' <> Vmap.find u' t'.map then swap t' u u' else t'
end
