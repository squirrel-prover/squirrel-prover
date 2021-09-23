
let hcombine acc n = acc * 65599 + n

let hcombine_list fhash hash l =
  List.fold_left (fun hash x -> 
      hcombine hash (fhash x)
    ) hash l

(* -------------------------------------------------------------------- *)
module Hashtbl = struct
  include Hashtbl

  let to_list (tbl : ('a, 'b) Hashtbl.t) : ('a * 'b) list = 
    Hashtbl.fold 
      (fun x y acc -> (x,y) :: acc)
      tbl
      []

  module Make2
      (H1:HashedType)
      (H2:HashedType) : S with type key = H1.t * H2.t = struct
    module H = struct
      type t = H1.t * H2.t

      let hash (t1,t2) = hcombine (H1.hash t1) (H2.hash t2)
      let equal (t1,t2) (t1',t2') = H1.equal t1 t1' && H2.equal t2 t2'
    end

    include Make (H)
  end
end

module List = struct
  include List

  let rec last = function
    | [] -> raise (Failure "List.last")
    | [x] -> x
    | _ :: l -> last l

  let init n f =
    if n < 0 then raise (Failure "List.init")
    else
      let rec ini i = if i = n then [] else (f i) :: ini (i + 1) in
      ini 0

  let merge_uniq cmp l1 l2 =
    match l1, l2 with
    | [], l2 -> l2
    | l1, [] -> l1
    | h1 :: t1, h2 :: t2 ->
      let c = cmp h1 h2 in
      if c = 0 then h1 :: merge cmp t1 t2
      else if c < 0
      then h1 :: merge cmp t1 l2
      else h2 :: merge cmp l1 t2

  let rec split3 = function
    | [] -> ([], [], [])
    | (x,y,z)::l ->
      let (rx, ry, rz) = split3 l in (x::rx, y::ry, z::rz)

  let inclusion a b =
    List.for_all (fun x -> List.mem x b)  a

  let rec assoc_up s f = function
    | [] -> raise Not_found
    | (a,b) :: t ->
      if a = s then (a, f b) :: t
      else (a,b) :: assoc_up s f t

  let rec assoc_up_dflt s dflt f = function
    | [] -> [s, f dflt]
    | (a,b) :: t ->
      if a = s then (a, f b) :: t
      else (a,b) :: assoc_up_dflt s dflt f t

  let rec assoc_dflt dflt x = function
    | [] -> dflt
    | (a,b)::l -> if compare a x = 0 then b else assoc_dflt dflt x l

  (*------------------------------------------------------------------*)
  let rec iteri2 i f l1 l2 =
    match (l1, l2) with
      ([], []) -> ()
    | (a1::l1, a2::l2) -> f i a1 a2; iteri2 (i+1) f l1 l2
    | (_, _) -> invalid_arg "List.iteri2"

  let iteri2 f l1 l2 = iteri2 0 f l1 l2

  (*------------------------------------------------------------------*)
  let rec drop0 i l =
    if i = 0 then l else
      match l with
      | _ :: t -> drop0 (i-1) t
      | [] -> l
        
  let drop i l =
    if i < 0 then failwith "invalid argument";
    drop0 i l

  (*------------------------------------------------------------------*)
  let rec take0 i l =
    if i = 0 then []
    else match l with
      | [] -> []
      | x :: t -> x :: take0 (i - 1) l
                    
  let rec take i l =
    if i < 0 then failwith "invalid argument";
    take0 i l

  (*------------------------------------------------------------------*)
  let rec takedrop0 l i r =
    if i = 0 then List.rev l, r
    else match r with
      | [] -> List.rev l, r
      | x :: t -> takedrop0 (x :: l) (i - 1) t

  let takedrop i l =
    if i < 0 then failwith "invalid argument";
    takedrop0 [] i l

  (*------------------------------------------------------------------*)
  exception Out_of_range
    
  let splitat i l =
    let rec aux i acc = function
      | [] -> raise Out_of_range
      | e::tl -> if i=0 then acc,e,tl else aux (i-1) (e::acc) tl
    in aux i [] l

  (*------------------------------------------------------------------*)
  let remove_duplicate cmp l =
    let l_rev = 
      List.fold_left (fun l el ->
          if List.exists (cmp el) l then l else el :: l
        ) [] l
    in
    List.rev l_rev  
end

(*------------------------------------------------------------------*)
module String = struct
  include String

  let get_integer s =
    try
      Some (int_of_string s)
    with Failure _ -> None

  let split_on_integer s =
    let res = ref None in
    let len =  (String.length s) in
    let l = ref (len - 1) in
    let cond = ref true in
    (* we start from the end of the string, and as soon as we don't recognize an
       integer anymore, we stop. *)
    while (!l >= 0) && !cond do
      let new_res = get_integer (String.sub s !l (len - !l)) in
      match new_res with
      | None -> cond := false
      | _ -> res:= new_res; decr l
    done;
    (String.sub s 0 (!l+1), !res)
end

(*------------------------------------------------------------------*)
module Mi = Map.Make (Int)
module Si = Set.Make (Int)

module Ms = Map.Make (String)
module Ss = Set.Make (String)


(*------------------------------------------------------------------*)
(* Option type functions *)

let some x = Some x

let oget = function
  | Some u -> u
  | None -> raise Not_found

let odflt dflt = function
  | Some u -> u
  | None -> dflt

let obind f a = match a with
  | None -> None
  | Some x -> f x

let omap f a = match a with
  | None -> None
  | Some x -> Some (f x)

let omap_dflt dflt f a = match a with
  | None -> dflt
  | Some x -> f x

let oiter f a = match a with
  | None -> ()
  | Some x -> f x

(*------------------------------------------------------------------*)
module type Ordered = sig
  type t
  val compare : t -> t -> int
  val print : Format.formatter -> t -> unit
end

(*------------------------------------------------------------------*)
(** Variable size persistent union-find data-structure on integers. *)
module Vuf : sig
  type t

  val create : int -> t

  (** Add a new element to the partition, which is alone in its class. *)
  val extend : t -> int * t

  val find : t -> int -> int

  (** [union t u v] always uses the representent of [v], i.e.
      [find [union t u v] u] = [find t v] *)
  val union : t -> int -> int -> t

end = struct

  (** Variable size persistent union-find, by leaving some unused elements:
      - [uf] contains a partition of [0,...,max_size - 1]
      - Only classes in [0,...,size-1] may be modified by union and find. *)
  type t = { uf : Puf.t;
             size : int;
             max_size : int }

  let create i =
    (* If [n] is 0 or 1, extend will fail. *)
    let n = max i 2 in
    { uf = Puf.create (2 * n); (* The factor 2 is arbitrary. *)
      size = n;
      max_size = 2 * n }

  let print ppf t =
    for i = 0 to t.max_size - 1 do
      let ri = Puf.find t.uf i in
      Fmt.pf ppf "@[%d->%d @]"
        i ri           
    done

  let extend t =
    if t.size < t.max_size then (t.size, { t with size = t.size + 1 })
    else
      begin
        let uf' = ref (Puf.create (t.max_size * 2)) in
        for i = 0 to t.size - 1 do
          (* ignore_rank ensure that thi right element is choosen as
             a representent of the set. *)
          uf' := Puf.union ~ignore_rank:true !uf' i (Puf.find t.uf i);
        done;
        (t.size, { uf = !uf'; size = t.size + 1; max_size = t.max_size * 2 } )
      end

  let find t i =
    if i >= t.size then raise (Failure "Vuf: out of range")
    else Puf.find t.uf i

  let union t i j =
    if i >= t.size || j >= t.size then raise (Failure "Vuf: out of range")
    else { t with uf = Puf.union t.uf i j }
end


module Uf (Ord: Ordered) = struct
  type v = Ord.t
  module Vmap = Map.Make(Ord)

  module Smart : sig 
    (** [rmap] is the inverse of map.
        [cpt] counts the number of non-trivial unions .
        [id] is guaranteed to be different for different union-find structures. *)
    type t = private { 
      map : int Vmap.t;
      rmap : v Mi.t;
      puf : Vuf.t;
      cpt : int;
      id : int; 
    }

    val mk : 
      ?map:(int Vmap.t) ->
      ?rmap:(v Mi.t) ->
      ?puf:Vuf.t ->
      ?cpt:int -> 
      t ->
      t

    val empty : int -> t

  end = struct
    type t = { map : int Vmap.t;
               rmap : v Mi.t;
               puf : Vuf.t;
               cpt : int;
               id : int; }

    let cpt_id = ref 0
    let mk_id () = incr cpt_id; !cpt_id
    
    let empty d = {
      map = Vmap.empty; 
      rmap = Mi.empty; 
      puf = Vuf.create d; 
      cpt = 0;
      id = mk_id (); 
    }

    let mk ?map ?rmap ?puf ?cpt t =
      let map  = odflt t.map map
      and rmap = odflt t.rmap rmap
      and puf  = odflt t.puf puf
      and cpt  = odflt t.cpt cpt in
      { map; rmap; puf; cpt; id = mk_id (); }
  end
  include Smart

  let print ppf t =
    let binds = Mi.bindings t.rmap
                |> List.sort (fun (i, _) (i', _) -> Stdlib.compare i i') in
    Fmt.pf ppf "@[<v 0>%a@]"
      (Fmt.list (fun ppf (i, u) ->
           let ri = Vuf.find t.puf i in
           Fmt.pf ppf "@[%d->%d : @,%a->%a@]"
             i ri Ord.print u Ord.print (Mi.find ri t.rmap)
         )) binds

  let create l =
    let _,m,rm =
      List.fold_left (fun ( i, m, rm ) a ->
          ( i+1, Vmap.add a i m, Mi.add i a rm ))
        ( 0, Vmap.empty, Mi.empty ) l
    in
    Smart.mk ~map:m ~rmap:rm ~cpt:0 (Smart.empty (List.length l))

  let id t = t.id

  (** [extend t v] add the element [v] to [t], if necessary. *)
  let extend t v =
    if Vmap.mem v t.map then t
    else
      let i, uf = Vuf.extend t.puf in
      Smart.mk ~puf:uf
               ~map:(Vmap.add v i t.map)
               ~rmap:(Mi.add i v t.rmap) 
               t

  let find t u =
    let ru_eqc = Vmap.find u t.map |> Vuf.find t.puf in
    Mi.find ru_eqc t.rmap

  let swap t u u' =
    let i = Vmap.find u t.map
    and i' = Vmap.find u' t.map in

    Smart.mk
      ~map:(Vmap.add u i' t.map
            |> Vmap.add u' i)
      ~rmap:(Mi.add i u' t.rmap
             |> Mi.add i' u) 
      t

  let union t u u' =
    let iu, iu' = Vmap.find u t.map, Vmap.find u' t.map in
    let ri, ri' = Vuf.find t.puf iu, Vuf.find t.puf iu' in
    let t' = 
      if ri <> ri' 
      then Smart.mk
        ~puf:(Vuf.union t.puf iu iu')
        ~cpt:(t.cpt + 1) 
        t
      else t
    in
    let n_ri' = Vmap.find u' t'.map |> Vuf.find t'.puf in
    if ri' <> n_ri' then swap t' u u' else t'

  let add_acc a acc = match acc with
    | [] -> raise (Failure "Uf: add_acc")
    | l :: t -> (a :: l) :: t


  let comp_classes t =
    let l = List.init (Mi.cardinal t.rmap) (fun i -> (Vuf.find t.puf i, i))
            |> List.sort (fun (a, _) (a', _) -> Stdlib.compare a a')
    in
    let l_eqc = match l with
      | [] -> []
      | (x, _) :: _ ->
        List.fold_left (fun (acc, x_old) (x, y) ->
            if x = x_old then (add_acc y acc, x)
            else ([y] :: acc, x)
          ) ([[]], x) l
        |> fst
    in
    List.map (List.map (fun x -> Mi.find x t.rmap)) l_eqc


  module MemoV = struct
    type _t = t
    type t = _t
    let hash t = t.id
    let equal t t' = t.id = t'.id
  end
  module Memo = Ephemeron.K1.Make(MemoV)
  module Memo2 (H2:Hashtbl.HashedType) = Ephemeron.K2.Make (MemoV) (H2)

  let memo_cl = Memo.create 256 

  (* memoisation *)
  let classes t = try Memo.find memo_cl t with
    | Not_found ->
      let cs = comp_classes t in
      Memo.add memo_cl t cs; 
      cs

  (** [union_count t] is the number of non-trivial unions done building [t] *)
  let union_count t = t.cpt
end


(*------------------------------------------------------------------*)
let rec fpt eq f a =
  let b = f a in
  if eq b a then b else fpt eq f b

(*------------------------------------------------------------------*)
let classes (f_eq : 'a -> 'a -> bool) (l : 'a list) : 'a list list =
  let rec get_cl cl rem x = function
    | [] -> cl,rem
    | y :: l ->
      if f_eq x y then get_cl (y :: cl) rem x l
      else get_cl cl (y :: rem) x l
  in
  let rec comp cls = function
    | [] -> cls
    | x :: rem ->
      let cl, rem' = get_cl [x] [] x rem in
      comp (cl :: cls) rem'
  in
  comp [] l

(*------------------------------------------------------------------*)
let ident ppf s = Fmt.pf ppf "%s" s
let kw style = (Fmt.styled style ident)

let pp_ne_list s pp_list ppf l =
  if l = [] then Fmt.pf ppf "" else Fmt.pf ppf s pp_list l

let sep ppf () = Fmt.pf ppf ",@,"

let pp_list pp_item ppf l =
  if l <> [] then
    Fmt.pf ppf "(@[<hov 1>%a@])"
      (Fmt.list ~sep pp_item) l

(*------------------------------------------------------------------*)
let fst3 (a, b, c) = a

(*------------------------------------------------------------------*)
type 'a timeout_r = 
  | Result of 'a 
  | Timeout
  
(** [timeout t f x] executes [f x] for at most [t] seconds.
    Returns [Result (f x)] if the computation terminated in the imparted
    time, and [Timeout] otherwise. *)
let timeout timeout f x =
  assert (timeout > 0);

  let exception Timeout in
  (* Set new handler, and store old one. *)
  let old_handler = Sys.signal Sys.sigalrm
    (Sys.Signal_handle (fun _ -> raise Timeout)) in

  let finish () =   
    (* Cancels the alarm:
     * "If seconds is zero, any pending alarm is canceled."
     * see: man 2 alarm *)
    ignore (Unix.alarm 0);
    (* Restores previous handler. *)
    ignore (Sys.signal Sys.sigalrm old_handler) in

  try
    (* Raises [Sys.sigalrm] after [timeout] seconds. *)
    ignore (Unix.alarm timeout);

    let res = f x in
    finish ();
    Result res
  with
  | Timeout -> finish (); Timeout
  | exn     -> finish (); raise exn

(* -------------------------------------------------------------------- *)
let as_seq0 = function [] -> ()                     | _ -> assert false
let as_seq1 = function [x] -> x                     | _ -> assert false
let as_seq2 = function [x1; x2] -> (x1, x2)         | _ -> assert false
let as_seq3 = function [x1; x2; x3] -> (x1, x2, x3) | _ -> assert false

let as_seq4 = function [x1; x2; x3; x4] -> (x1, x2, x3, x4)
  | _ -> assert false

