open Ppenv

module SE = SystemExpr
module Sv = Term.Sv

 (*------------------------------------------------------------------*)
type bound =
  | Glob                   (** a global proof-term *)
  | ReachAsym              (** a local asymptotic proof-term *)
  | ReachConc of Term.term (** a local concrete proof-term *)

let from_option ?(conc = ReachAsym) ( b : Term.term option) : bound =
  match b with
  | None -> conc
  | Some e -> ReachConc e

let to_option ( b : bound ) : Term.term option =
  match b with
  | Glob | ReachAsym -> None
  | ReachConc e -> Some e

let get ( b : bound ) : Term.term  =
  match b with
  | Glob | ReachAsym -> assert false
  | ReachConc e -> e

let map_term (f : Term.t -> Term.t) (b : bound): bound =
  match b with
  | Glob | ReachAsym -> b
  | ReachConc e -> ReachConc (f e)

(*------------------------------------------------------------------*)
let _pp ppe fmt = function
  | Glob      -> Fmt.pf fmt "global proof-term"
  | ReachAsym   -> Fmt.pf fmt "local asymptotic proof-term"
  | ReachConc b -> 
    Fmt.pf fmt "@[<hov 2>local concrete proof-term with bound:@ @[%a@]@]" 
      (Term._pp ppe) b

let pp     = _pp (default_ppe ~dbg:false ())
let pp_dbg = _pp (default_ppe ~dbg:true ())

(*------------------------------------------------------------------*)
let equal (b1 : bound) (b2 : bound) : bool =
  match b1, b2 with
  | Glob      , Glob       -> true
  | ReachAsym   , ReachAsym    -> true
  | ReachConc t1, ReachConc t2 -> Term.equal t1  t2
  | _                      -> false

let fv (b : bound) : Sv.t =
  match b with
  | Glob | ReachAsym -> Sv.empty
  | ReachConc t -> Term.fv t

(*------------------------------------------------------------------*)
let is_zero (table : Symbols.table) (b : bound)  : bool =
  match b with
  | Glob -> false
  | ReachAsym -> false
  | ReachConc t1 -> Real.is_zero table t1

let is_asym (table : Symbols.table) (b : bound) : bool =
  match b with
  | Glob -> false
  | ReachAsym -> true
  | ReachConc t1 -> Real.is_zero table t1

let is_concrete (b : bound) : bool =
  match b with
  | Glob | ReachAsym -> false
  | ReachConc _ -> true

let ge_zero (table : Symbols.table) (b : bound)  : bool =
  match b with
  | Glob -> false
  | ReachAsym -> false
  | ReachConc t1 -> Real.ge_zero table t1

(*Check if the bound [b1] entail the bound [b2]
   Could be massively improved.
*)
let entails table system b1 b2 =
  let module R : ReductionCore.Sig =
    (val ReductionCore.Register.get ())
  in
  let state =
    R.mk_state0
      ~system ~red_param:ReductionCore.rp_default ~concrete:true
      table
  in
  match b1,b2 with
  | ReachAsym, ReachAsym -> true
  | ReachConc e, ReachAsym ->
    Real.is_zero table (R.reduce_term state e)
  | ReachConc ve, ReachConc e -> R.conv state ve e
  | Glob, Glob -> true
  | _ -> false

(*------------------------------------------------------------------*)
let bound_projs projs = function
  | ReachConc t -> ReachConc (Term.project projs t)
  | _ as f -> f

let bound_subst_projs (projs : (Projection.t * Projection.t) list) = function
  | ReachConc t -> ReachConc (Term.subst_projs projs t)
  | _ as f -> f

let subst subst = function
  | ReachConc t -> ReachConc (Term.subst subst t)
  | _ as f -> f

let gsubst subst = function
  | ReachConc t -> ReachConc (Term.gsubst subst t)
  | _ as f -> f

(*------------------------------------------------------------------*)
