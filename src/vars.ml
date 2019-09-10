module type VarParam = sig
  val default_string : string
  val cpt : int ref
end

type var = {id:int;name:string }

module type VarType = sig
  type t
  val make_fresh : unit -> t
  val pp : Format.formatter -> t -> unit
  val pp_list : Format.formatter -> t list -> unit
end

module Var(V:VarParam) : VarType = 
  struct
    type t = var

    let make_fresh () =
      let id = !V.cpt - 1 in
      incr V.cpt; {id = id; name =  Format.sprintf "%s_%i" V.default_string id }

    let pp ppf v =
      Fmt.pf ppf "%s" v.name
                      
    let pp_list ppf l =
      Fmt.pf ppf "@[<hov>%a@]"
        (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",") pp) l
 end
