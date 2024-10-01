module Mid = Ident.Mid

(*------------------------------------------------------------------*)             
type t = {
  univars : Type.ty Ident.Mid.t;
  tvars   : Type.ty Ident.Mid.t;
}

type 'a substitution = t -> 'a -> 'a

(*------------------------------------------------------------------*)
let pp_subst fmt ts =
  let pp_bd fmt (id,ty) =
    Fmt.pf fmt "@[%a → %a@]" Ident.pp_full id Type.pp ty
  in
  Fmt.pf fmt "@[<v 0>@[<hov 2>univars:@ %a@]@;@[<hov 2>tvars:@ %a@]@]"
    (Fmt.list ~sep:Fmt.comma pp_bd) (Mid.bindings ts.univars)
    (Fmt.list ~sep:Fmt.comma pp_bd) (Mid.bindings ts.tvars)

(*------------------------------------------------------------------*)
(** {2 Building substitutions } *)

let empty_subst =
  { univars = Mid.empty;
    tvars   = Mid.empty; }

let mk_subst ~(tvars:Type.ty Mid.t) ~(univars:Type.ty Mid.t) : t =
  { univars;
    tvars; }

(*------------------------------------------------------------------*)
let add_tvar   s tv ty = { s with tvars   = Mid.add tv ty s.tvars; }
let add_univar s tu ty = { s with univars = Mid.add tu ty s.univars; }

(*------------------------------------------------------------------*)
(** {2 Substitution functions} *)

(*------------------------------------------------------------------*)
let subst_ty (s : t) (t : Type.ty) : Type.ty =
  let rec doit (t : Type.ty) =
    match t with
    | Message | Boolean | Index | Timestamp | TBase _ -> t

    | TVar id -> Mid.find_dflt t id s.tvars

    | TUnivar ui -> Mid.find_dflt t ui s.univars

    | Tuple tys -> Type.tuple (List.map doit tys)
    | Fun (t1, t2) -> Type.func (doit t1) (doit t2)
  in
  doit t

(*------------------------------------------------------------------*)
let subst_var (s : t) (v : Vars.var) : Vars.var =
  Vars.mk v.id (subst_ty s v.ty)

(*------------------------------------------------------------------*)
let subst_ftype (ts : t) (fty : Type.ftype) : Type.ftype = 
  Type.{
    fty_vars = fty.fty_vars;              (* bound type variable *)
    fty_args = List.map (subst_ty ts) fty.fty_args;
    fty_out  = subst_ty ts fty.fty_out;
  }
