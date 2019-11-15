module type VarParam =
sig
  val default_string : string
end

type var = {id : int; name : string}

module type VarType =
sig
  type t
  val reset_id_names : unit -> unit
  val make_fresh : ?name:string -> unit -> t
  val get_or_make_fresh : t list -> string -> t
  val name : t -> string
  val pp : Format.formatter -> t -> unit
  val pp_list : Format.formatter -> t list -> unit
end

module Var(V:VarParam) : VarType =
struct
  type t = var

  let cpt = ref 0

  module M = Map.Make(String)

  let idnames = ref M.empty

  let reset_id_names () =
     idnames := M.empty

  let next_id name =
    if M.mem name !idnames then
      begin
        let curr = 1+(M.find name !idnames) in
        idnames := M.add name curr !idnames;
        curr
      end
    else
      begin
        idnames := M.add name 0 !idnames;
        0
      end

  let make_fresh ?(name=V.default_string) () =
    let id = !cpt in
    incr cpt;
    let idname = next_id name in
      { id = id;
        name =
          if idname = 0 then
            name
          else
            Format.sprintf "%s_%i" name idname
      }

  let make_fresh_by_name (n:string) =
    let id = !cpt in
    incr cpt;
      { id = id;
        name =  n }

  let get_or_make_fresh (ts:t list) (n:string) =
    match List.filter (fun t -> t.name = n) ts with
    |  [] -> make_fresh_by_name n
    | p::q -> p

  let name v =
    v.name

  let pp ppf v =
    Fmt.pf ppf "%s" v.name

  let pp_list ppf l =
    Fmt.pf ppf "@[<hov>%a@]"
      (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") pp) l
end

module TParam : VarParam =
struct
  let default_string = "tau"
end

module Tvar = Var(TParam)


module MParam : VarParam =
struct
  let default_string = "mes"
end

module Mvar = Var(MParam)

module IndexParam : VarParam =
struct
  let default_string = "idx"
end

module Index : VarType = Var(IndexParam)

let reset_id_names () =
  Tvar.reset_id_names ();
  Mvar.reset_id_names ();
  Index.reset_id_names ()
