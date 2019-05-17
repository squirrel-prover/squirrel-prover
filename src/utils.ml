module List = struct
  include List

  (** [init n f] returns the list containing the results of
      [(f 0)],[(f 1)] ... [(f (n-1))].  *)
  let init n f =
    if n < 0 then raise (Failure "List.init")
    else
      let rec ini i = if i = n then [] else (f i) :: ini (i + 1) in
      ini 0
end

module Imap = Map.Make (struct
  type t = int
  let compare = Pervasives.compare
end)

module type Ordered = sig
  type t
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end

(** Create a union-find data-structure over elements of type 'a. *)
module Uf (Ord: Ordered) = struct
  type v = Ord.t
  module Vmap = Map.Make(Ord)
  (* [rmap] is the inverse of map.
     [cpt] counts the number of non-trivial unions *)
  type t = { map : int Vmap.t;
             rmap : v Imap.t;
             puf : Puf.t;
             cpt : int }

  let print ppf t =
    let binds = Imap.bindings t.rmap
                |> List.sort (fun (i,_) (i',_) -> Pervasives.compare i i') in
    Fmt.pf ppf "@[<v 0>%a@]"
      (Fmt.list (fun ppf (i,u) ->
           Fmt.pf ppf "@[%d->%d : @,%a@]" i (Puf.find t.puf i) Ord.print u
         )) binds

  let create l =
    let _,m,rm =
      List.fold_left (fun ( i, m, rm ) a ->
          ( i+1, Vmap.add a i m, Imap.add i a rm ))
        ( 0, Vmap.empty, Imap.empty ) l in

    { map = m;
      rmap = rm;
      puf = Puf.create (List.length l);
      cpt = 0 }

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
    let iu,iu' = Vmap.find u t.map, Vmap.find u' t.map in
    let ri,ri' = Puf.find t.puf iu, Puf.find t.puf iu' in

    let t' = { t with puf = Puf.union t.puf iu iu';
                      cpt = if ri <> ri' then t.cpt + 1 else t.cpt } in

    let n_ri' = Vmap.find u' t'.map |> Puf.find t'.puf in

    if ri' <> n_ri' then swap t' u u' else t'

  let add_acc a acc = match acc with
    | [] -> raise (Failure "Uf: add_acc")
    | l :: t -> (a :: l) :: t

  (** [classes t] return the list of equivalence classes of [t], where a class
      is represented by the list of its elements. *)
  let classes t =
    let l = List.init (Imap.cardinal t.rmap) (fun i -> (Puf.find t.puf i, i))
            |> List.sort (fun (a,_) (a',_) -> Pervasives.compare a a') in

    let l_eqc = match l with
      | [] -> []
      | (x,_) :: _ ->
        List.fold_left (fun (acc,x_old) (x,y) ->
            if x = x_old then (add_acc y acc, x)
            else ([y] :: acc, x)
          ) ([[]], x) l
        |> fst in

    List.map (List.map (fun x -> Imap.find x t.rmap)) l_eqc

  (** [union_count t] is the number of non-trivial unions done building [t] *)
  let union_count t = t.cpt
end


(* Option type functions *)
let opt_get = function
  | Some u -> u
  | None -> raise Not_found


let some x = Some x
