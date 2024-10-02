open Ppenv

(*------------------------------------------------------------------*)
type bound = 
  | Glob                 (** a global hypothesis/lemma *)
  | LocAsym              (** a local asymptotic proof-term *)
  | LocHyp               (** when [form] comes from a local hypothesis (in a concrete judgement) *)
  | LocConc of Term.term (** a local concrete lemma *)

(*------------------------------------------------------------------*)
let _pp ppe fmt = function
  | Glob      -> Fmt.pf fmt "global"
  | LocAsym   -> Fmt.pf fmt "local asymptotic"
  | LocHyp    -> Fmt.pf fmt "local concrete (from hypotheses)"
  | LocConc b -> Fmt.pf fmt "local concrete (bound = %a)" (Term._pp ppe) b

let pp     = _pp (default_ppe ~dbg:false ())
let pp_dbg = _pp (default_ppe ~dbg:true ())

(*------------------------------------------------------------------*)
let equal (b1 : bound) (b2 : bound) : bool =
  match b1, b2 with
  | Glob      , Glob       -> true
  | LocAsym   , LocAsym    -> true
  | LocHyp    , LocHyp     -> true
  | LocConc t1, LocConc t2 -> Term.equal t1 t2
  | _                      -> false

(*------------------------------------------------------------------*)
let bound_projs projs = function
  | LocConc t -> LocConc (Term.project projs t)
  | _ as f -> f

let bound_subst_projs (projs : (Projection.t * Projection.t) list) = function
  | LocConc t -> LocConc (Term.subst_projs projs t)
  | _ as f -> f

let bound_gsubst subst = function
  | LocConc t -> LocConc (Term.gsubst subst t)
  | _ as f -> f

