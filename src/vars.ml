module type VarParam = sig
  val default_string : string
  val cpt : int ref
end

type var = {id:int;name:string }

module type VarType = sig
  type t
  val make_fresh : ?name:string -> unit -> t
  val get_or_make_fresh : t list -> string -> t
  val pp : Format.formatter -> t -> unit
  val pp_list : Format.formatter -> t list -> unit
end

module Var(V:VarParam) : VarType = 
  struct
    type t = var

    let make_fresh ?(name=V.default_string) () =
      let id = !V.cpt in
      incr V.cpt; {id = id; name =  Format.sprintf "%s" name }

    let get_or_make_fresh (ts:t list) (n:string) =
      match List.filter (fun t -> t.name = n) ts with
        [] -> make_fresh ~name:n ()
      | p::q -> p
    
    let pp ppf v =
      Fmt.pf ppf "%s" v.name
                      
    let pp_list ppf l =
      Fmt.pf ppf "@[<hov>%a@]"
        (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") pp) l
 end
