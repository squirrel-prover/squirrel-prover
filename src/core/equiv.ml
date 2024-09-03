(** Equivalence formulas.  *)

open Utils
open Ppenv
    
module Sv = Vars.Sv
module Mv = Vars.Mv

module SE = SystemExpr
  
(*------------------------------------------------------------------*)
(** {2 Equivalence} *)

type equiv = {terms : Term.term list; bound : Term.term option}

(*------------------------------------------------------------------*)
let _pp_terms ppe fmt (terms : Term.term list) =
  Fmt.pf fmt "@[%a@]"
    (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt ",@ ") (Term._pp ppe))
    terms

let _pp_equiv ppe fmt ({terms; bound} : equiv)= match bound with
  | Some ve -> Fmt.pf fmt "equiv(%a) <: %a" (_pp_terms ppe) terms (Term._pp ppe) ve
  | None ->     Fmt.pf fmt "equiv(%a)" (_pp_terms ppe) terms

let pp_equiv = _pp_equiv (default_ppe ~dbg:false ())

(*------------------------------------------------------------------*)
let _pp_equiv_numbered ppe fmt (l : equiv) =
  List.iteri (fun i elem ->
    Fmt.pf fmt "%i: @[%a@]@;" i (Term._pp ppe) elem
    ) l.terms ;
  Option.iter (Fmt.pf fmt "bound: @[%a@]@;" (Term._pp ppe)) l.bound

let pp_equiv_numbered = _pp_equiv_numbered (default_ppe ~dbg:false ())

(*------------------------------------------------------------------*)
let subst_equiv (subst : Term.subst) (e : equiv) : equiv =
  {terms = List.map (Term.subst subst) e.terms;
   bound = Option.map (Term.subst subst) e.bound}

let tsubst_equiv (subst : Type.tsubst) (e : equiv) : equiv =
  {terms = List.map (Term.tsubst subst) e.terms;
   bound = Option.map (Term.tsubst subst) e.bound}

let subst_projs_equiv (subst : (Term.proj * Term.proj) list) (e : equiv) : equiv =
  {terms = List.map (Term.subst_projs subst) e.terms;
   bound = Option.map (Term.subst_projs subst) e.bound}

(** Free variables of an [equiv]. *)
let fv_equiv e : Sv.t =
  Sv.union
    (List.fold_left (fun sv elem ->
      Sv.union sv (Term.fv elem)
    ) Sv.empty e.terms)
    (Option.value ~default:Sv.empty (Option.map Term.fv e.bound))

(** Free type variables of an [equiv]. *)
let ty_fv_equiv e : Type.Fv.t =
  Type.Fv.union
    (List.fold_left (fun sv elem ->
      Type.Fv.union sv (Term.ty_fv elem)
     ) Type.Fv.empty e.terms)
    (Option.value ~default:Type.Fv.empty (Option.map Term.ty_fv e.bound))

(*------------------------------------------------------------------*)
(** {2 Formula with potential upper bound} *)

type bform = {formula : Term.term; bound : Term.term option}

(*------------------------------------------------------------------*)
let _pp_bform_conclusion ppe fmt = function
  | {formula; bound = Some ve} -> 
    Fmt.pf fmt "@[%a@]@;bound : @[%a@]@;" (Term._pp ppe) formula (Term._pp ppe) ve
  | {formula; bound = None} -> 
    Fmt.pf fmt "@[%a@]" (Term._pp ppe) formula

let _pp_bform ppe fmt = function
  | {formula; bound = Some ve} -> 
    Fmt.pf fmt "@[%a <: %a@]" (Term._pp ppe) formula (Term._pp ppe) ve
  | {formula; bound = None} -> 
    Fmt.pf fmt "@[%a@]" (Term._pp ppe) formula

let equal_bform (f : bform) (g : bform) : bool =
  match f.bound, g.bound with
  | Some e, Some ve -> Term.equal f.formula g.formula && Term.equal e ve
  | None, None -> Term.equal f.formula g.formula
  | _ -> false

let subst_bform (subst : Term.subst) (f : bform) : bform =
  { formula = Term.subst subst f.formula; 
    bound   = Option.map (Term.subst subst) f.bound}

let tsubst_bform (subst : Type.tsubst) (f : bform) : bform =
  { formula = Term.tsubst subst f.formula;
    bound   = Option.map (Term.tsubst subst) f.bound}

let subst_projs_bform (subst : (Term.proj * Term.proj) list) (f : bform) : bform =
  { formula = Term.subst_projs subst f.formula; 
    bound   = Option.map (Term.subst_projs subst) f.bound}

let proj_bform (subst : Term.proj list) (f : bform) : bform =
  { formula = Term.project subst f.formula; 
    bound   = Option.map (Term.project subst) f.bound}

(** Free variables of a [formula]. *)
let fv_bform f : Sv.t =
  Sv.union 
    (Term.fv f.formula)
    (Option.value (Option.map Term.fv f.bound) ~default:Sv.empty)

(** Free type variables of a [formula]. *)
let ty_fv_bform f : Type.Fv.t =
  Type.Fv.union (Term.ty_fv f.formula)
    (Option.value (Option.map Term.ty_fv f.bound) ~default:Type.Fv.empty)

(*------------------------------------------------------------------*)
(** {2 User-defined predicate} *)

type pred_app = {
  psymb      : Symbols.predicate;        (** Predicate symbol *)
  ty_args    : Type.ty list;             (** Type arguments *)
  se_args    : SE.t list;                (** System expression arguments *)  
  multi_args : (SE.t * Term.terms) list;
  (** Multi-term args with their system expression. *)
  simpl_args : Term.terms;
  (** Simple arguments, not a multi-term. *)
}

(*------------------------------------------------------------------*)
(** Print the system arguments of a predicate application
    ([context.set] and [context.pair] are implicit and ignored
    when possible). *)

let _pp_pred_app ?context ppe fmt p =
  let pp_se_args ?context fmt se_args =
    (* Tedious.
       Remove up-to the first two arguments, if they are equal
       to [set] or [equiv] *)
    let se_args =
      match context with
      | None -> se_args
      | Some context ->
        match se_args, context.SE.pair with
        | [set; equiv], Some pair ->
          if SE.equal0 set   context.SE.set &&
             SE.equal0 equiv (pair :> SE.t) then [] else se_args
        | [set], _ ->
          if SE.equal0 set context.SE.set then [] else [set]
        | se_args, _ -> se_args
    in
    if se_args = [] then () else
      Fmt.pf fmt "{%a}"
        (Fmt.list ~sep:(Fmt.any "@ ") (Fmt.brackets SE.pp))
        se_args
  in
  let pp_ty_args ppe fmt ty_args =
    if not ppe.dbg || ty_args = [] then () else
      Fmt.pf fmt "@[<hov 2><%a>@]"
        (Fmt.list ~sep:Fmt.comma Type.pp) ty_args
  in
  match p with
  | { psymb; ty_args; se_args; multi_args; simpl_args }
    when Symbols.is_infix_predicate psymb ->
    let bl,br = as_seq2 (List.concat_map snd multi_args @ simpl_args) in
    let pp fmt () =
      Fmt.pf fmt "@[<0>$(%a %a%a%a@ %a)@]"
        (Term._pp ppe) bl
        Symbols.pp_path psymb
        (pp_ty_args ppe) ty_args
        (pp_se_args ?context) se_args
        (Term._pp ppe) br
    in
    pp fmt ()

  | { psymb; ty_args; se_args; multi_args; simpl_args } ->
    let pp_args fmt =
      let all_args = List.concat_map snd multi_args @ simpl_args in
      Fmt.list ~sep:(Fmt.any "@ ") (Term._pp ppe) fmt all_args
    in
      Fmt.pf fmt "@[%a%a%a %t@]"
        Symbols.pp_path psymb
        (pp_ty_args ppe) ty_args
        (pp_se_args ?context) se_args
        pp_args 

let subst_pred_app (subst : Term.subst) (pa : pred_app) : pred_app = {
  psymb      = pa.psymb;
  ty_args    = pa.ty_args;
  se_args    = pa.se_args;
  multi_args =
    List.map (fun (se,args) -> se, List.map (Term.subst subst) args) pa.multi_args;
  simpl_args = List.map (Term.subst subst) pa.simpl_args;
}

let fv_pred_app (pa : pred_app) =
  let fv =
    List.fold_left (fun fv (_,args) ->
        Sv.union fv (Term.fvs args)
      ) Sv.empty pa.multi_args
  in
  Sv.union fv (Term.fvs pa.simpl_args)

let ty_fv_pred_app (pa : pred_app) =
  let fv =
    List.fold_left (fun fv (_,args) ->
        Type.Fv.union fv (Term.ty_fvs args)
      ) Type.Fv.empty pa.multi_args
  in
  Type.Fv.union fv (Term.ty_fvs pa.simpl_args)

let tsubst_pred_app (ts : Type.tsubst) (pa : pred_app) : pred_app = {
  psymb      = pa.psymb;
  ty_args    = List.map (Type.tsubst ts) pa.ty_args;
  se_args    = pa.se_args;
  multi_args =
    List.map (fun (se,args) -> se, List.map (Term.tsubst ts) args) pa.multi_args;
  simpl_args = List.map (Term.tsubst ts) pa.simpl_args;
}

 (*------------------------------------------------------------------*)
(** {2 Equivalence atoms} *)

 (** See `.mli` *)
type atom =
  | Equiv of equiv
  | Reach of bform
  | Pred of pred_app
    

let _pp_atom_conclusion ppe ?context fmt (l : atom) =
  match l with
  | Equiv e -> _pp_equiv_numbered ppe fmt e
  | Reach f -> _pp_bform_conclusion ppe fmt f
  | Pred p -> _pp_pred_app ?context ppe fmt p


let _pp_atom ppe ?context fmt = function
  | Equiv e -> _pp_equiv ppe fmt e
  | Reach f ->  Fmt.pf fmt "[%a]" (_pp_bform ppe) f
  | Pred p -> _pp_pred_app ?context ppe fmt p

let pp_atom = _pp_atom (default_ppe ~dbg:false ()) ?context:None

(*------------------------------------------------------------------*)

let subst_atom (subst : Term.subst) (a : atom) : atom =
  match a with
  | Equiv e  -> Equiv (subst_equiv subst e)
  | Reach f  -> Reach (subst_bform subst f)
  | Pred  pa -> Pred  (subst_pred_app subst pa)

(*------------------------------------------------------------------*)

(** Free variables of an [atom]. *)
let fv_atom = function
  | Equiv e -> fv_equiv e
  | Reach f -> fv_bform f
  | Pred  pa -> fv_pred_app pa

(*------------------------------------------------------------------*)

(** Free type variables of an [atom]. *)
let ty_fv_atom = function
  | Equiv e -> ty_fv_equiv e
  | Reach f -> ty_fv_bform f
  | Pred  pa -> ty_fv_pred_app pa


(** Type substitution of an [atom]*)
let tsubst_atom (ts : Type.tsubst) (at : atom) =
  match at with
  | Equiv e -> Equiv (tsubst_equiv ts e)
  | Reach f -> Reach (tsubst_bform ts f)
  | Pred  pa -> Pred  (tsubst_pred_app ts pa)
(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)
(** We only support a small fragment for now *)

type quant = ForAll | Exists

let pp_quant fmt = function
  | ForAll -> Fmt.pf fmt "Forall"
  | Exists -> Fmt.pf fmt "Exists"

type form =
  | Quant of quant * Vars.tagged_vars * form
  | Let   of Vars.var * Term.term * form
  | Atom  of atom
  | Impl  of form * form
  | And   of form * form
  | Or    of form * form

let equal : form -> form -> bool = (=)

(*------------------------------------------------------------------*)
(** Free variables. *)
let rec fv = function
  | Atom at -> fv_atom at
  | And  (f, f0)
  | Or   (f, f0)
  | Impl (f, f0) -> Sv.union (fv f) (fv f0)
  | Quant (_, evs, b) -> Sv.diff (fv b) (Sv.of_list (List.map fst evs))
  | Let (v,t,f) -> Sv.union (Term.fv t) (Sv.remove v (fv f))

(*------------------------------------------------------------------*)
(** Free type variables. *)
let rec ty_fv = function
  | Atom at -> ty_fv_atom at
  | And  (f, f0)
  | Or   (f, f0)
  | Impl (f, f0) -> Type.Fv.union (ty_fv f) (ty_fv f0)
  | Quant (_, evs, b) -> 
    Type.Fv.diff (ty_fv b) (Vars.ty_fvs (List.map fst evs))
  | Let (v,t,f) -> Type.Fv.union (Vars.ty_fv v) (Type.Fv.union (Term.ty_fv t) (ty_fv f))
                     
let ty_fvs l = List.fold_left (fun fv e -> Type.Fv.union fv (ty_fv e)) Type.Fv.empty l

(*------------------------------------------------------------------*)
let mk_quant0_tagged q (evs : Vars.tagged_vars) f =
  match evs, f with
  | [], _ -> f
  | _, Quant (q', evs', f) when q = q' -> Quant (q, evs @ evs', f)
  | _, _ -> Quant (q, evs, f)

let%test_unit _ =
  let f = Atom (Equiv {terms = []; bound = None}) in
  let v1 = [Vars.make_fresh Type.Message "x",Vars.Tag.ltag] in
  let v2 = [Vars.make_fresh Type.Message "y",Vars.Tag.ltag] in
  assert (mk_quant0_tagged ForAll [] f = f) ;
  assert (mk_quant0_tagged ForAll v1 f = Quant (ForAll,v1,f)) ;
  assert (f |> mk_quant0_tagged ForAll v2
            |> mk_quant0_tagged ForAll v1 =
          Quant (ForAll, v1@v2, f)) ;
  assert (f |> mk_quant0_tagged ForAll v2
            |> mk_quant0_tagged Exists v1 =
          Quant (Exists,v1,Quant (ForAll,v2,f)))

let mk_reach_atom ?e f = Atom (Reach {formula = f; bound = e } )
let mk_equiv_atom ?e f = Atom (Equiv {terms = f; bound = e } )
                             
(*------------------------------------------------------------------*)
(** {2 Map (does not recurse) } *)

(** Does not recurse. *)
let tmap (func : form -> form) (t : form) : form =

  let tmap = function
    | Quant (q, vs, b) -> Quant (q, vs, func b)
    | Let (v,t,f) -> Let (v, t, func f)
    | Impl (f1, f2) -> Impl (func f1, func f2)
    | And  (f1, f2) -> And  (func f1, func f2)
    | Or   (f1, f2) -> Or   (func f1, func f2)

    | Atom at       -> Atom at
  in
  tmap t

(*------------------------------------------------------------------*)
(* FIXME: perf *)
    
let tmap_fold : ('b -> form -> 'b * form) -> 'b -> form -> 'b * form =
  fun func b t ->
  let bref = ref b in
  let g t =
    let b, t = func !bref t in
    bref := b;
    t
  in
  let t = tmap g t in
  !bref, t

let titer (f : form -> unit) (t : form) : unit =
  let g e = f e; e in
  ignore (tmap g t)

let tforall (f : form -> bool) (t : form) : bool =
  let x = ref true in
  let g e = x := (!x && f e); e in
  ignore (tmap g t);
  !x

let texists (f : form -> bool) (t : form) : bool =
  let x = ref false in
  let g e = x := (!x || f e); e in
  ignore (tmap g t);
  !x

let tfold : (form -> 'b -> 'b) -> form -> 'b -> 'b =
  fun f t v ->
  let vref : 'b ref = ref v in
  let fi e = vref := (f e !vref) in
  titer fi t;
  !vref

(*------------------------------------------------------------------*)
(** {2 Substitution} *)

(* FIXME: perf *)
let rec subst s (f : form) =
  if s = [] ||
     (Term.is_var_subst s &&
      Sv.disjoint (Term.subst_support s) (fv f))
  then f
  else
    match f with
    | Atom at -> Atom (subst_atom s at)

    | Quant (_, [], f) -> subst s f
    | Quant (q, (v,tag) :: evs, b) ->
      let v, s = Term.subst_binding v s in
      let f = subst s (Quant (q, evs,b)) in
      mk_quant0_tagged q [v,tag] f

    | Let (v,t,f) ->
      let t = Term.subst s t in
      let v, s = Term.subst_binding v s in
      let f = subst s f in
      Let (v,t,f)
      
    | _ -> tmap (subst s) f

(*------------------------------------------------------------------*)
(** Projection substitution *)

let subst_projs_atom 
    (target : [`Equiv | `Reach]) 
    (s : (Term.proj * Term.proj) list) (at : atom) : atom 
  =
  match at with
  | Equiv e ->
    if target = `Equiv
    then Equiv (subst_projs_equiv s e)
    else at
      
  | Reach f ->
    if target = `Reach
    then Reach (subst_projs_bform s f)
    else at

  (* FIXME: allow to substitute projections in predicates *)
  (* | Pred { psymb; ty_args; se_args; multi_args; simpl_args } -> *)
  (*   Pred { *)
  (*     psymb; ty_args; *)
  (*     se_args = List.map (SE.subst_projs s) se_args; *)
  (*     multi_args = *)
  (*       List.map (fun (se,args) -> *)
  (*           ( SE.subst_projs s se, *)
  (*             List.map (Term.subst_projs s) args) *)
  (*         ) multi_args; *)
  (*     simpl_args = List.map (Term.subst_projs s) simpl_args; *)
  (*   } *)

  | Pred _ -> at

let subst_projs
    (target : [`Equiv | `Reach]) 
    (s : (Term.proj * Term.proj) list) (t : form) : form 
  =
  let rec doit = function
    | Atom at -> Atom (subst_projs_atom target s at)
    | _ as term -> tmap doit term
  in

  doit t

(*------------------------------------------------------------------*)
(** Type substitutions *)


let tsubst (ts : Type.tsubst) (t : form) =
  let rec tsubst = function
    | Quant (q, vs, f) ->
      Quant (q, List.map (fst_bind (Vars.tsubst ts)) vs, tsubst f)
    | Let (v, t, f) ->
      Let (Vars.tsubst ts v, Term.tsubst ts t, tsubst f)
    | Atom at -> Atom (tsubst_atom ts at)
    | _ as term -> tmap tsubst term
  in

  tsubst t

(*------------------------------------------------------------------*)
(** System variable substitutions *)

let se_subst_pred_app (s : SE.subst) (pa : pred_app) : pred_app = {
  psymb      = pa.psymb;
  ty_args    = pa.ty_args;
  se_args    = List.map (SE.subst s) pa.se_args;
  multi_args =
    List.map (fun (se,args) -> SE.subst s se, args) pa.multi_args;
  simpl_args = pa.simpl_args;
}

let se_subst_atom (s : SE.subst) (at : atom) =
  match at with
  | Equiv _ | Reach _ -> at
  | Pred pa -> Pred (se_subst_pred_app s pa)

let se_subst (s : SE.subst) (t : form) =
  let rec se_subst = function
    | Atom at -> Atom (se_subst_atom s at)
    | _ as term -> tmap se_subst term
  in
  se_subst t

(*------------------------------------------------------------------*)
(** {2 Pretty printing} *)

let toplevel_prec = 0
let quant_fixity  = 5  , `Prefix
let let_in_fixity = 5  , `Prefix
let impl_fixity   = 10 , `Infix `Right
let or_fixity     = 20 , `Infix `Right
let and_fixity    = 25 , `Infix `Right

(** Internal *)
let pp (ppe : ppenv) ?context pp_atom = 
  let rec pp 
      pp_atom
      ((outer,side) : ('b * fixity) * assoc)
      (fmt : Format.formatter)
    = function
      | Atom at -> pp_atom ppe ?context fmt at

      | Impl (f0, f) ->
        let pp fmt () = 
          Fmt.pf fmt "@[<0>%a ->@ %a@]"
            (pp _pp_atom (impl_fixity, `Left)) f0
            (pp _pp_atom (impl_fixity, `Right)) f
        in
        maybe_paren ~outer ~side ~inner:impl_fixity pp fmt ()

      | And (f0, f) ->
        let pp fmt () =     
          Fmt.pf fmt "@[<0>%a /\\@ %a@]" 
            (pp _pp_atom (and_fixity, `Left)) f0
            (pp _pp_atom (and_fixity, `Right)) f
        in
        maybe_paren ~outer ~side ~inner:and_fixity pp fmt ()

      | Or (f0, f) ->
        let pp fmt () = 
          Fmt.pf fmt "@[<0>%a \\/@ %a@]"
            (pp _pp_atom (or_fixity, `Left)) f0
            (pp _pp_atom (or_fixity, `Right)) f
        in
        maybe_paren ~outer ~side ~inner:or_fixity pp fmt ()

      | Let (v,t,f) ->
        let _, v, s = (* rename quantified var. to avoid name clashes *)
          let fv_ts = Sv.remove v (fv f) in
          Term.add_vars_simpl_env (Vars.of_set fv_ts) [v]
        in
        let v = as_seq1 v in
        let f = subst s f in

        let pp fmt () =
          Fmt.pf fmt "@[<hov 0>Let %a =@;<1 2>@[%a@]@ in@ %a@]"
            (Vars._pp ppe) v
            (Term._pp ppe) t
            (pp _pp_atom (let_in_fixity, `NonAssoc)) f
        in
        maybe_paren ~outer ~side ~inner:let_in_fixity pp fmt ()

      | Quant (bd, vs0, f) ->
        let _, vs, s = (* rename quantified vars. to avoid name clashes *)
          let fv_f = List.fold_left ((^~) (fst_map Sv.remove)) (fv f) vs0 in
          Term.add_vars_simpl_env (Vars.of_set fv_f) (List.map fst vs0)
        in
        let f = subst s f in

        let pp fmt () = 
          Fmt.pf fmt "@[<2>%a (@[%a@]),@ %a@]"
            pp_quant bd
            (Vars._pp_typed_tagged_list ppe)
            (List.map2 (fun v (_, tag) -> v,tag) vs vs0)
            (pp _pp_atom (quant_fixity, `Right)) f
        in
        maybe_paren ~outer ~side ~inner:(fst quant_fixity, `Prefix) pp fmt ()
  in
  pp pp_atom

let pp_toplevel ?context ppe pp_atom (fmt : Format.formatter) (f : form) : unit =
  pp ppe ?context pp_atom ((toplevel_prec, `NoParens), `NonAssoc) fmt f
    
(** Exported *)
let _pp    = fun ?context ppe -> pp_toplevel ?context ppe _pp_atom
let pp     = pp_toplevel (default_ppe ~dbg:false ()) ?context:None _pp_atom
let pp_dbg = pp_toplevel (default_ppe ~dbg:true  ()) ?context:None _pp_atom

let _pp_conclusion   = fun ?context ppe -> pp_toplevel ?context ppe _pp_atom_conclusion

(*------------------------------------------------------------------*)
(** {2 Misc} *)

let is_constant ?(env : Env.t option) (t : Term.term) : bool =
  let env = odflt (Env.init ~table:(Symbols.builtins_table ()) ()) env in
  HighTerm.is_constant env t

let is_system_indep
    ?(env : Env.t = Env.init ~table:(Symbols.builtins_table ()) ())
    (t    : Term.term)
  : bool
  =
  HighTerm.is_system_indep env t
let rec get_terms = function
  | Atom (Reach f) -> f.formula::(Option.to_list f.bound)
  | Atom (Equiv e) -> Option.to_list e.bound  @ e.terms
  | Atom (Pred pa) -> List.concat_map snd pa.multi_args @ pa.simpl_args
  | And  (e1, e2)
  | Or   (e1, e2)
  | Impl (e1, e2) -> get_terms e1 @ get_terms e2
  | Let _ | Quant _ -> []

(*------------------------------------------------------------------*)
let rec is_system_context_indep (f : form) : bool =
  match f with
  | Atom (Equiv _ | Reach _) -> false
  | _ -> tforall is_system_context_indep f

(*------------------------------------------------------------------*)
let rec project (projs : Term.proj list) (f : form) : form =
  match f with
  | Atom (Reach f) -> Atom (Reach (proj_bform projs f))

  | _ -> tmap (project projs) f
    
(*------------------------------------------------------------------*)
let mk_quant_tagged ?(simpl=false) q (l : Vars.tagged_vars) f =
  let l =
    if simpl then
      let fv = fv f in
      List.filter (fun (v,_) -> Sv.mem v fv) l
    else l
  in
  mk_quant0_tagged q l f

(*------------------------------------------------------------------*)
(** {2 Smart constructors and destructors} *)
type _form = form

(* TODO: factorize with code in Term.ml ? *)
module Smart : SmartFO.S with type form = _form = struct
  type form = _form

  let todo () = Tactics.soft_failure (Failure "not implemented")
  (** {3 Constructors} *)
  let mk_true = Atom (Reach {formula = Term.mk_true; bound = None})
  let mk_false = Atom (Reach {formula = Term.mk_false; bound = None})

  let[@warning "-27"] mk_not ?simpl f = todo ()

  (*------------------------------------------------------------------*)
  let[@warning "-27"] mk_and ?simpl f1 f2 = And (f1, f2)

  let[@warning "-27"] rec mk_ands ?(simpl = false) forms =
    match forms with
    | [] -> mk_true
    | [f0] -> f0
    | f0 :: forms -> 
      And (f0, mk_ands forms)

  (*------------------------------------------------------------------*)
  let[@warning "-27"] mk_or ?simpl f1 f2 = Or (f1, f2)

  let[@warning "-27"] rec mk_ors ?simpl forms =
    match forms with
    | [] -> mk_false
    | [f0] -> f0
    | f0 :: forms -> Or (f0, mk_ors forms)

  (*------------------------------------------------------------------*)
  let[@warning "-27"] mk_impl ?simpl f1 f2 = Impl (f1, f2)

  let[@warning "-27"] rec mk_impls ?simpl l f =
    match l with
    | [] -> f
    | f0 :: impls -> Impl (f0, mk_impls impls f)

  (*------------------------------------------------------------------*)
  let mk_forall_tagged ?simpl = mk_quant_tagged ?simpl ForAll
  let mk_exists_tagged ?simpl = mk_quant_tagged ?simpl Exists

  let mk_forall ?simpl vs =
    mk_quant_tagged ?simpl ForAll (List.map (fun v -> v, Vars.Tag.gtag) vs)
  let mk_exists ?simpl vs =
    mk_quant_tagged ?simpl Exists (List.map (fun v -> v, Vars.Tag.gtag) vs)

  (*------------------------------------------------------------------*)
  let mk_eq  ?simpl f1 f2 = Atom (Reach {formula = (Term.Smart.mk_eq  ?simpl f1 f2); bound = None})
  let mk_neq ?simpl f1 f2 = Atom (Reach {formula = (Term.Smart.mk_neq ?simpl f1 f2); bound = None})
  let mk_leq        f1 f2 = Atom (Reach {formula = (Term.Smart.mk_leq f1 f2); bound = None})
  let mk_geq        f1 f2 = Atom (Reach {formula = (Term.Smart.mk_geq f1 f2); bound = None})
  let mk_lt  ?simpl f1 f2 = Atom (Reach {formula = (Term.Smart.mk_lt  ?simpl f1 f2); bound = None})
  let mk_gt  ?simpl f1 f2 = Atom (Reach {formula = (Term.Smart.mk_gt  ?simpl f1 f2); bound = None})

  (*------------------------------------------------------------------*)
  let mk_let ?(simpl = false) v t f =
    if simpl && not (Sv.mem v (fv f))
    then f
    else Let (v,t,f)

  (*------------------------------------------------------------------*)
  (** {3 Destructors} *)

  let destr_quant_tagged ?env q = function
    | Quant (q', es, f) when q = q' -> Some (es, f)

    (* case [f = ∃es. f0], check that:
       - [f] is constant
       - [f0] is system-independant *)
    (*TODO : kind, check this for multiterms*)
    (*TODO:Concrete : Check if valid of concrete*)
    | Atom (Reach {formula = f; bound}) when q = Exists && is_constant ?env f ->
        begin match Term.Smart.destr_exists_tagged f with
          | Some (es,f) when is_system_indep ?env f ->
            Some (es, Atom (Reach {formula = f;bound}))
          | _ -> None
        end

    (*TODO : kind, check this for multiterms*)
    | Atom (Reach {formula = f; bound}) when q = ForAll ->
        begin match Term.Smart.destr_forall_tagged f with
          | Some (es,f) -> Some (es, Atom (Reach {formula = f; bound}))
          | None -> None
        end

    | _ -> None

  let destr_forall_tagged      = destr_quant_tagged      ForAll
  let destr_exists_tagged ?env = destr_quant_tagged ?env Exists

  let destr_forall f =
    omap (fun (vs, f) -> List.map fst vs, f) (destr_quant_tagged ForAll f)

  let destr_exists ?env f =
    omap (fun (vs, f) -> List.map fst vs, f) (destr_quant_tagged ?env Exists f)
  
  (*------------------------------------------------------------------*)
  let destr_quant1_tagged ?env q = function
    | Quant (q', (v,tag) :: es, f) when q = q' ->
      Some ((v, tag), mk_quant_tagged q es f)

    (* case [f = ∃es. f0], check that:
       - [f] is constant
       - [f0] is system-independant *)
    (*TODO:Concrete : Check if valid of concrete*)
    | Atom (Reach {formula = f; bound}) when q = Exists && is_constant ?env f ->
        begin match Term.Smart.destr_exists1_tagged f with
          | Some (es,f) when is_system_indep ?env f ->
            Some (es, Atom (Reach {formula = f; bound}))
          | _ -> None
        end

    (* For a local meta-formula f,
       (Forall x. [f]) is equivalent to [forall x. f]. *)
    | Atom (Reach {formula = f; bound}) when q = ForAll ->
      begin match Term.Smart.destr_forall1_tagged f with
          | Some (es,f) -> Some (es, Atom (Reach {formula = f; bound}))
          | None -> None
        end

    | _ -> None

  let destr_forall1_tagged      = destr_quant1_tagged      ForAll
  let destr_exists1_tagged ?env = destr_quant1_tagged ?env Exists

  let destr_forall1 f =
    omap (fun (vs, f) -> fst vs, f) (destr_quant1_tagged ForAll f)
      
  let destr_exists1 ?env f =
    omap (fun (vs, f) -> fst vs, f) (destr_quant1_tagged ?env Exists f)

  (*------------------------------------------------------------------*)
  let destr_let = function
    | Let (v,t,f) -> Some (v,t,f)
    | _ -> None

  (*------------------------------------------------------------------*)
  let destr_false _f = todo ()
  let destr_true  _f = todo ()
  let destr_not   _f = todo ()

  (*TODO:Concrete : Check if valid of concrete*)
  let destr_and = function
    | And (f1, f2) -> Some (f1, f2)
    | Atom (Reach {formula = f; bound = None}) ->
        begin match Term.Smart.destr_and f with
          | Some (f1,f2) ->
             Some
               (Atom (Reach {formula = f1; bound = None}),
                Atom (Reach {formula = f2; bound = None}))
          | None -> None
        end
    | _ -> None

  (*TODO:Concrete : Check if valid of concrete*)
  let destr_or ?env = function
    | Or (f1, f2) -> Some (f1, f2)
    | Atom (Reach {formula = f; bound}) ->
       begin match Term.Smart.destr_or f with
         | Some (f1,f2) when
             (is_constant ?env f1 && is_system_indep ?env f1) ||
             (is_constant ?env f2 && is_system_indep ?env f2)
           ->
             Some (Atom (Reach {formula = f1; bound}), Atom (Reach {formula = f2; bound}))
         | _ -> None
       end
    | _ -> None

  (*TODO:Concrete : Check if valid of concrete*)
  let destr_impl ?env = function
    | Impl (f1, f2) -> Some (f1, f2)
    | Atom (Reach {formula = f; bound = None}) ->
       begin match Term.Smart.destr_impl f with
         | Some (f1,f2) when
             is_constant ?env f1 && is_system_indep ?env f1 ->
             Some (Atom (Reach {formula = f1; bound = None}), Atom (Reach {formula = f2; bound = None}))
         | _ -> None
       end
    | _ -> None

  (*TODO:Concrete : Check if valid of concrete*)
  let destr_iff = function
    | Atom (Reach {formula = f; bound}) ->
       begin match Term.Smart.destr_iff f with
         | Some (f1,f2) ->
             Some (Atom (Reach {formula = f1; bound}), Atom (Reach {formula = f2; bound}))
         | _ -> None
       end
    | _ -> None

  (*------------------------------------------------------------------*)

  (** left-associative *)
  let[@warning "-32"] mk_destr_left f_destr =
    let rec destr l f =
      if l < 0 then assert false;
      if l = 1 then Some [f]
      else match f_destr f with
        | None -> None
        | Some (f,g) -> omap (fun l -> l @ [g]) (destr (l-1) f)
    in
    destr

  (** right-associative *)
  let mk_destr_right f_destr =
    let rec destr l f =
      if l < 0 then assert false;
      if l = 1 then Some [f]
      else match f_destr f with
        | None -> None
        | Some (f,g) -> omap (fun l -> f :: l) (destr (l-1) g)
    in
    destr

  let destr_ands i f = mk_destr_right destr_and i f

  let destr_ors ?env i f = mk_destr_right (destr_or ?env) i f

  let destr_impls i f = mk_destr_right destr_impl i f

  (*TODO:Concrete : Check if it is necessary to add the bounded case*)
  let destr_eq = function
    | Atom (Reach {formula = f; bound = None}) -> Term.destr_eq f
    | _ -> None

  let destr_neq = function
    | Atom (Reach {formula = f; bound = None}) -> Term.destr_eq f
    | _ -> None

  let destr_leq = function
    | Atom (Reach {formula = f; bound = None}) -> Term.destr_eq f
    | _ -> None

  let destr_lt = function
    | Atom (Reach {formula = f; bound = None}) -> Term.destr_eq f
    | _ -> None

  (*------------------------------------------------------------------*)
  (*TODO:Concrete : Not valid for concrete*)
  let is_false _f = todo ()
  let is_true  _f = todo ()
  let is_not   _f = false       (* FIXME *)
  let is_and       f = destr_and       f <> None
  let is_or   ?env f = destr_or   ?env f <> None
  let is_impl ?env f = destr_impl ?env f <> None
  let is_iff       f = destr_iff       f <> None
  let is_let       f = destr_let       f <> None
  
  let is_forall      f = destr_forall      f <> None
  let is_exists ?env f = destr_exists ?env f <> None

  let is_eq  f = destr_eq  f <> None
  let is_neq f = destr_neq f <> None
  let is_leq f = destr_leq f <> None
  let is_lt  f = destr_lt  f <> None

  (*------------------------------------------------------------------*)
  let rec decompose_quant_tagged q = function
    | Quant (q', es, f) when q = q' ->
      let es', f = decompose_quant_tagged q f in
      es @ es', f

    (* For a local meta-formula f,
     * (Forall x. [f]) is equivalent to [forall x. f]. *)
    | Atom (Reach {formula = f; bound}) when q = ForAll ->
      let es,f = Term.Smart.decompose_forall_tagged f in
      es, Atom (Reach {formula = f; bound})

    | _ as f -> [], f

  let decompose_forall_tagged = decompose_quant_tagged ForAll
  let decompose_exists_tagged = decompose_quant_tagged Exists

  let decompose_forall f =
    let vs, f = decompose_quant_tagged ForAll f in
    List.map fst vs, f

  let decompose_exists f =
    let vs, f = decompose_quant_tagged Exists f in
    List.map fst vs, f
 
  (*------------------------------------------------------------------*)
  let decompose_ands (f : form) : form list  =
    let rec doit acc = function
      | And (f1,f2) -> doit (doit acc f2) f1
      | _ as f -> f :: acc
    in
    doit [] f

  let decompose_ors (f : form) : form list  =
    let rec doit acc = function
      | Or (f1,f2) -> doit (doit acc f2) f1
      | _ as f -> f :: acc
    in
    doit [] f

  let decompose_impls f =
    let rec decompose f = match destr_impl f with
      | None -> [f]
      | Some (f,g) -> f :: decompose g
    in
    decompose f

  let decompose_impls_last f =
    let forms = decompose_impls f in
    let rec last = function
      | [] -> assert false
      | [f] -> [], f
      | f :: fs ->
        let prems, goal = last fs in
        f :: prems, goal
    in
    last forms
end

let destr_reach = function
  | Atom (Reach f) -> Some f
  | _ -> None

let is_reach f = destr_reach f <> None
                 
let destr_equiv = function
  | Atom (Equiv t) -> Some t
  | _ -> None

let is_equiv f = destr_equiv f <> None

(*------------------------------------------------------------------*)
(** {2 Generalized formulas} *)

type any_form = Global of form | Local of Term.term

let _pp_any_form ppe fmt (f : any_form) =
  match f with
  | Global e -> _pp ppe fmt e
  | Local f -> Term._pp ppe fmt f

let pp_any_form     = _pp_any_form (default_ppe ~dbg:false ()) 
let pp_any_form_dbg = _pp_any_form (default_ppe ~dbg:true ())  

let any_to_reach (f : any_form) : Term.term =
  match f with
  | Global _ -> assert false
  | Local f -> f

let any_to_equiv (f : any_form) : form =
  match f with
  | Global f -> f
  | Local _ -> assert false

let is_local = function
  | Local  _ -> true
  | Global _ -> false

let is_global = function
  | Local  _ -> false
  | Global _ -> true

(*------------------------------------------------------------------*)
type local_form = Term.term
type global_form = form

type _ f_kind =
  | Local_t  : local_form  f_kind
  | Global_t : global_form f_kind
  | Any_t    : any_form    f_kind

let kind_equal (type a b) (k1 : a f_kind) (k2 : b f_kind) : bool =
  match k1, k2 with
  | Local_t,  Local_t  -> true
  | Global_t, Global_t -> true
  | Any_t, Any_t       -> true
  | _ -> false

(** Module Any without conversion functions. *)
module PreAny = struct

  type t = any_form

  let pp fmt = function
    | Local  f -> Term.pp fmt f
    | Global f ->      pp fmt f

  let _pp ?context ppe fmt = function
    | Local  f -> Term._pp ppe          fmt f
    | Global f ->      _pp ppe ?context fmt f

  let pp_dbg fmt = function
    | Local  f -> Term.pp_dbg fmt f
    | Global f ->      pp_dbg fmt f

  let equal x y = match x,y with
    | Local f, Local g  -> Term.equal f g
    | Global f, Global g ->  equal f g
    | _ -> false

  let subst s = function
    | Local  f -> Local  (Term.subst s f)
    | Global f -> Global (     subst s f)

  let tsubst s = function
    | Local  f -> Local  (Term.tsubst s f)
    | Global f -> Global (     tsubst s f)

  let subst_projs target s = function
    | Local f -> 
      if target = `Reach then 
        Local (Term.subst_projs s f)
      else 
        Local f
    | Global f -> Global (subst_projs target s f)

  let fv = function
    | Local  f -> Term.fv f
    | Global f -> fv f

  let ty_fv = function
    | Local  f -> Term.ty_fv f
    | Global f -> ty_fv f

  let get_terms = function
    | Local f  -> [f]
    | Global f -> get_terms f

  let project p = function
    | Local f  -> Local  (Term.project p f)
    | Global f -> Global (     project p f)
end

module Babel = struct

  let convert (type a b) ?loc ~(src:a f_kind) ~(dst:b f_kind) (f : a) : b
    = 
    match src,dst with
      (* Identity cases *)
      | Local_t,  Local_t  -> f
      | Global_t, Global_t -> f
      | Any_t,    Any_t    -> f

      (* Injections into [any_form] *)
      | Local_t,  Any_t -> Local f
      | Global_t, Any_t -> Global f

      (* Inverses of the injections. *)
      | Any_t, Local_t ->
        begin match f with
          | Global (Atom (Reach f)) -> f.formula
          | Local f -> f
          | _ -> Tactics.soft_failure ?loc CannotConvert
        end

      | Any_t, Global_t ->
        begin match f with
          | Global f -> f
          | Local f -> Atom (Reach {formula = f; bound = None})
        end

      (* Conversions between local and global formulas. *)
      | Local_t,  Global_t -> Atom (Reach {formula = f; bound = None})
      | Global_t, Local_t  ->
        begin match f with
          | Atom (Reach f) -> f.formula
          | _ -> Tactics.soft_failure ?loc CannotConvert
        end

  let subst : type a. a f_kind -> Term.subst -> a -> a = function
    | Local_t  -> Term.subst
    | Global_t -> subst
    | Any_t    -> PreAny.subst

  let subst_projs : 
    type a. a f_kind -> [`Equiv | `Reach] -> (Term.proj * Term.proj) list -> a -> a 
    =
    fun kind target s f ->
    match kind with
    | Local_t  ->   Term.subst_projs        s f
    | Global_t ->        subst_projs target s f
    | Any_t    -> PreAny.subst_projs target s f

  let tsubst : type a. a f_kind -> Type.tsubst -> a -> a = function
    | Local_t  -> Term.tsubst
    | Global_t -> tsubst
    | Any_t    -> PreAny.tsubst

  let fv : type a. a f_kind -> a -> Vars.Sv.t = function
    | Local_t  -> Term.fv
    | Global_t -> fv
    | Any_t    -> PreAny.fv


  let get_terms : type a. a f_kind -> a -> Term.term list = function
    | Local_t  -> fun f -> [f]
    | Global_t -> get_terms
    | Any_t    -> PreAny.get_terms
(*TODO:Concrete : Do the pretty printer for local formula*)
  let pp : type a. a f_kind -> Format.formatter -> a -> unit = function
    | Local_t  -> Term.pp
    | Global_t -> pp
    | Any_t    -> PreAny.pp

  let pp_dbg : type a. a f_kind -> Format.formatter -> a -> unit = function
    | Local_t  -> Term.pp_dbg
    | Global_t -> pp_dbg
    | Any_t    -> PreAny.pp_dbg

  let project : type a. a f_kind -> Term.proj list -> a -> a = function
    | Local_t  -> Term.project
    | Global_t -> project
    | Any_t    -> PreAny.project

end

module Any = struct

  include PreAny

  let convert_from k f =
    Babel.convert ~src:k ~dst:Any_t f

  let convert_to ?loc k f =
    Babel.convert ?loc ~dst:k ~src:Any_t f

  module Smart : SmartFO.S with type form = any_form = struct
    type form = any_form

    let mk_true  = Local Term.mk_true
    let mk_false = Local Term.mk_false

    let mk_not ?simpl f =
      match f with
        | Local f  -> Local  (Term.Smart.mk_not ?simpl f)
        | Global f -> Global (     Smart.mk_not ?simpl f)

    let mk_and ?simpl f g =
      match f,g with
        | Local  f, Local  g -> Local  (Term.Smart.mk_and ?simpl f g)
        | Global f, Global g -> Global (     Smart.mk_and ?simpl f g)
        | _ -> assert false

    let mk_or ?simpl f g =
      match f,g with
        | Local  f, Local  g -> Local  (Term.Smart.mk_or ?simpl f g)
        | Global f, Global g -> Global (     Smart.mk_or ?simpl f g)
        | _ -> assert false

    let mk_impl ?simpl f g : any_form =
      match f,g with
        | Local  f, Local  g -> Local  (Term.Smart.mk_impl ?simpl f g)
        | Global f, Global g -> Global (     Smart.mk_impl ?simpl f g)
        | _ -> assert false

    let mk_ands ?simpl = function
      | [] -> Local (Term.Smart.mk_ands ?simpl [])
      | (Local _ :: _) as l ->
          let l = List.map (function Local f -> f | _ -> assert false) l in
          Local (Term.Smart.mk_ands ?simpl l)
      | (Global _ :: _) as l ->
          let l = List.map (function Global f -> f | _ -> assert false) l in
          Global (Smart.mk_ands ?simpl l)

    let mk_ors ?simpl = function
      | [] -> Local (Term.Smart.mk_ors ?simpl [])
      | (Local _ :: _) as l ->
          let l = List.map (function Local f -> f | _ -> assert false) l in
          Local (Term.Smart.mk_ors ?simpl l)
      | (Global _ :: _) as l ->
          let l = List.map (function Global f -> f | _ -> assert false) l in
          Global (Smart.mk_ors ?simpl l)

    let mk_impls ?simpl l f = match l,f with
      | [],Local f -> Local(Term.Smart.mk_impls ?simpl [] f)
      | [],Global f -> Global (Smart.mk_impls ?simpl [] f)
      | (Local _ :: _) as l, Local f ->
          let l = List.map (function Local f -> f | _ -> assert false) l in
          Local (Term.Smart.mk_impls ?simpl l f)
      | (Global _ :: _) as l, Global f ->
          let l = List.map (function Global f -> f | _ -> assert false) l in
          Global (Smart.mk_impls ?simpl l f)
      | _ -> assert false

    let mk_eq  ?simpl f g = Local (Term.Smart.mk_eq  ?simpl f g)
    let mk_neq ?simpl f g = Local (Term.Smart.mk_neq ?simpl f g)
    let mk_leq        f g = Local (Term.Smart.mk_leq        f g)
    let mk_geq       f g = Local (Term.Smart.mk_geq        f g)
    let mk_lt  ?simpl f g = Local (Term.Smart.mk_lt  ?simpl f g)
    let mk_gt  ?simpl f g = Local (Term.Smart.mk_gt  ?simpl f g)

    (*------------------------------------------------------------------*)
    let mk_let ?simpl v t1 = function
      | Local  t2 -> Local  (Term.Smart.mk_let ?simpl v t1 t2)
      | Global t2 -> Global (     Smart.mk_let ?simpl v t1 t2)

    (*------------------------------------------------------------------*)
    let mk_forall ?simpl vs = function
      | Local  f -> Local  (Term.Smart.mk_forall ?simpl vs f)
      | Global f -> Global (     Smart.mk_forall ?simpl vs f)

    let mk_exists ?simpl vs = function
      | Local  f -> Local  (Term.Smart.mk_exists ?simpl vs f)
      | Global f -> Global (     Smart.mk_exists ?simpl vs f)

    (*------------------------------------------------------------------*)
    let mk_forall_tagged ?simpl vs = function
      | Local  f -> Local  (Term.Smart.mk_forall_tagged ?simpl vs f)
      | Global f -> Global (     Smart.mk_forall_tagged ?simpl vs f)

    let mk_exists_tagged ?simpl vs = function
      | Local  f -> Local  (Term.Smart.mk_exists_tagged ?simpl vs f)
      | Global f -> Global (     Smart.mk_exists_tagged ?simpl vs f)

    (*------------------------------------------------------------------*)
    let destr_forall1 = function
      | Local  f -> omap (fun (vs,f) -> vs, Local  f) (Term.Smart.destr_forall1 f)
      | Global f -> omap (fun (vs,f) -> vs, Global f) (     Smart.destr_forall1 f)

    let destr_exists1 ?env = function
      | Local  f -> omap (fun (vs,f) -> vs, Local  f) (Term.Smart.destr_exists1      f)
      | Global f -> omap (fun (vs,f) -> vs, Global f) (     Smart.destr_exists1 ?env f)

    let destr_forall = function
      | Local  f -> omap (fun (vs,f) -> vs, Local  f) (Term.Smart.destr_forall f)
      | Global f -> omap (fun (vs,f) -> vs, Global f) (     Smart.destr_forall f)

    let destr_exists ?env = function
      | Local  f -> omap (fun (vs,f) -> vs, Local  f) (Term.Smart.destr_exists      f)
      | Global f -> omap (fun (vs,f) -> vs, Global f) (     Smart.destr_exists ?env f)

    (*------------------------------------------------------------------*)
    let destr_forall1_tagged = function
      | Local  f -> omap (fun (vs,f) -> vs, Local  f) (Term.Smart.destr_forall1_tagged f)
      | Global f -> omap (fun (vs,f) -> vs, Global f) (     Smart.destr_forall1_tagged f)

    let destr_exists1_tagged ?env = function
      | Local  f -> omap (fun (vs,f) -> vs, Local  f) (Term.Smart.destr_exists1_tagged      f)
      | Global f -> omap (fun (vs,f) -> vs, Global f) (     Smart.destr_exists1_tagged ?env f)

    let destr_forall_tagged = function
      | Local  f -> omap (fun (vs,f) -> vs, Local  f) (Term.Smart.destr_forall_tagged f)
      | Global f -> omap (fun (vs,f) -> vs, Global f) (     Smart.destr_forall_tagged f)

    let destr_exists_tagged ?env = function
      | Local  f -> omap (fun (vs,f) -> vs, Local  f) (Term.Smart.destr_exists_tagged      f)
      | Global f -> omap (fun (vs,f) -> vs, Global f) (     Smart.destr_exists_tagged ?env f)

    (*------------------------------------------------------------------*)
    let destr_false = function
      | Local  f -> Term.Smart.destr_false f
      | Global f ->      Smart.destr_false f

    let destr_true = function
      | Local  f -> Term.Smart.destr_true f
      | Global f ->      Smart.destr_true f

    let destr_not = function
      | Local  f -> omap (fun f -> Local  f) (Term.Smart.destr_not f)
      | Global f -> omap (fun f -> Global f) (     Smart.destr_not f)

    let destr_and = function
      | Local  f -> omap (fun (x,y) -> Local  x, Local  y) (Term.Smart.destr_and f)
      | Global f -> omap (fun (x,y) -> Global x, Global y) (     Smart.destr_and f)

    let destr_or ?env = function
      | Local  f -> omap (fun (x,y) -> Local  x, Local  y) (Term.Smart.destr_or      f)
      | Global f -> omap (fun (x,y) -> Global x, Global y) (     Smart.destr_or ?env f)

    let destr_impl ?env = function
      | Local  f -> omap (fun (x,y) -> Local  x, Local  y) (Term.Smart.destr_impl      f)
      | Global f -> omap (fun (x,y) -> Global x, Global y) (     Smart.destr_impl ?env f)

    let destr_iff =  function
      | Local  f -> omap (fun (x,y) -> Local  x, Local  y) (Term.Smart.destr_iff f)
      | Global f -> omap (fun (x,y) -> Global x, Global y) (     Smart.destr_iff f)


    (*------------------------------------------------------------------*)
    let is_false = function
      | Local  f -> Term.Smart.is_false f
      | Global f ->      Smart.is_false f

    let is_true = function
      | Local  f -> Term.Smart.is_true f
      | Global f ->      Smart.is_true f

    let is_not = function
      | Local  f -> Term.Smart.is_not f
      | Global f ->      Smart.is_not f

    let is_and = function
      | Local  f -> Term.Smart.is_and f
      | Global f ->      Smart.is_and f

    let is_or ?env = function
      | Local  f -> Term.Smart.is_or      f
      | Global f ->      Smart.is_or ?env f

    let is_impl ?env = function
      | Local  f -> Term.Smart.is_impl      f
      | Global f ->      Smart.is_impl ?env f

    let is_iff = function
      | Local  f -> Term.Smart.is_iff f
      | Global f ->      Smart.is_iff f

    let is_forall = function
      | Local  f -> Term.Smart.is_forall f
      | Global f ->      Smart.is_forall f

    let is_exists ?env = function
      | Local  f -> Term.Smart.is_exists      f
      | Global f ->      Smart.is_exists ?env f

    let is_let = function
      | Local  f -> Term.Smart.is_let f
      | Global f ->      Smart.is_let f

    let is_eq = function
      | Local  f -> Term.Smart.is_eq f
      | Global f ->      Smart.is_eq f

    let is_neq = function
      | Local  f -> Term.Smart.is_neq f
      | Global f ->      Smart.is_neq f

    let is_leq = function
      | Local  f -> Term.Smart.is_leq f
      | Global f ->      Smart.is_leq f

    let is_lt = function
      | Local  f -> Term.Smart.is_lt f
      | Global f ->      Smart.is_lt f

    (*------------------------------------------------------------------*)
    let destr_let = function
      | Local f ->
        omap (fun (v,t1,t2) -> v,t1, Local t2) (Term.Smart.destr_let f)
      | Global f ->
        omap (fun (v,t1,t2) -> v,t1, Global t2) (     Smart.destr_let f)

    let destr_ands i = function
      | Local f ->
          omap (fun l -> List.map (fun x -> Local x) l)
            (Term.Smart.destr_ands i f)
      | Global f ->
          omap (fun l -> List.map (fun x -> Global x) l)
            (Smart.destr_ands i f)

    let destr_ors ?env i = function
      | Local f ->
          omap (fun l -> List.map (fun x -> Local x) l)
            (Term.Smart.destr_ors i f)
      | Global f ->
          omap (fun l -> List.map (fun x -> Global x) l)
            (Smart.destr_ors ?env i f)

    let destr_impls i = function
      | Local f ->
          omap (fun l -> List.map (fun x -> Local x) l)
            (Term.Smart.destr_impls i f)
      | Global f ->
          omap (fun l -> List.map (fun x -> Global x) l)
            (Smart.destr_impls i f)

    let destr_eq = function
      | Local  f -> Term.Smart.destr_eq f
      | Global f ->      Smart.destr_eq f

    let destr_neq = function
      | Local  f -> Term.Smart.destr_neq f
      | Global f ->      Smart.destr_neq f

    let destr_leq = function
      | Local  f -> Term.Smart.destr_leq f
      | Global f ->      Smart.destr_leq f

    let destr_lt = function
      | Local  f -> Term.Smart.destr_lt f
      | Global f ->      Smart.destr_lt f

    (*------------------------------------------------------------------*)
    let decompose_forall = function
      | Local f ->
        let vs,f = Term.Smart.decompose_forall f in
        vs, Local f
      | Global f ->
        let vs,f = Smart.decompose_forall f in
        vs, Global f

    let decompose_forall_tagged = function
      | Local f ->
        let vs,f = Term.Smart.decompose_forall_tagged f in
        vs, Local f
      | Global f ->
        let vs,f = Smart.decompose_forall_tagged f in
        vs, Global f

    (*------------------------------------------------------------------*)
    let decompose_exists = function
      | Local f ->
        let vs,f = Term.Smart.decompose_exists f in
        vs, Local f
      | Global f ->
        let vs,f = Smart.decompose_exists f in
        vs, Global f

    let decompose_exists_tagged = function
      | Local f ->
        let vs,f = Term.Smart.decompose_exists_tagged f in
        vs, Local f
      | Global f ->
        let vs,f = Smart.decompose_exists_tagged f in
        vs, Global f

    (*------------------------------------------------------------------*)
    let decompose_ands = function
      | Local  f -> List.map (fun x -> Local  x) (Term.Smart.decompose_ands f)
      | Global f -> List.map (fun x -> Global x) (     Smart.decompose_ands f)

    let decompose_ors = function
      | Local  f -> List.map (fun x -> Local  x) (Term.Smart.decompose_ors f)
      | Global f -> List.map (fun x -> Global x) (     Smart.decompose_ors f)

    let decompose_impls = function
      | Local  f -> List.map (fun x -> Local  x) (Term.Smart.decompose_impls f)
      | Global f -> List.map (fun x -> Global x) (     Smart.decompose_impls f)

    let decompose_impls_last = function
      | Local f ->
          let l,f = Term.Smart.decompose_impls_last f in
            List.map (fun x -> Local x) l, Local f
      | Global f ->
          let l,f = Smart.decompose_impls_last f in
            List.map (fun x -> Global x) l, Global f
  end

end

(*------------------------------------------------------------------*)
(** {2 Generalized statement} *)

type any_statement = GlobalS of form | LocalS of bform

let pp_any_statement ppe fmt (f : any_statement) =
  match f with
  | GlobalS e -> _pp       ppe fmt e
  | LocalS  f -> _pp_bform ppe fmt f

let any_statement_to_reach (f : any_statement) : bform =
  match f with
  | GlobalS _ -> assert false
  | LocalS f -> f

let any_statement_to_equiv (f : any_statement) : form =
  match f with
  | GlobalS f -> f
  | LocalS _ -> assert false

let is_local_statement = function
  | LocalS  _ -> true
  | GlobalS _ -> false

(*------------------------------------------------------------------*)
type _ s_kind =
  | Local_s  : bform  s_kind
  | Global_s : form s_kind
  | Any_s    : any_statement s_kind

let s_kind_equal (type a b) (k1 : a s_kind) (k2 : b s_kind) : bool =
  match k1, k2 with
  | Local_s,  Local_s  -> true
  | Global_s, Global_s -> true
  | Any_s, Any_s       -> true
  | _ -> false

(** Module Any without conversion functions. *)
module PreAny_statement = struct

  type t = any_statement

  let _pp ?context ppe fmt = function
    | LocalS  f -> _pp_bform ppe          fmt f
    | GlobalS f -> _pp       ppe ?context fmt f

  let pp     = _pp (default_ppe ~dbg:false ()) 
  let pp_dbg = _pp (default_ppe ~dbg:true  ()) 

  let equal x y = match x,y with
    | LocalS  f, LocalS  g -> equal_bform f g
    | GlobalS f, GlobalS g -> equal       f g
    | _ -> false

  let subst s = function
    | LocalS  f -> LocalS  (subst_bform s f)
    | GlobalS f -> GlobalS (      subst s f)

  let tsubst s = function
    | LocalS  f -> LocalS  (tsubst_bform s f)
    | GlobalS f -> GlobalS (      tsubst s f)

  let subst_projs target s = function
    | LocalS f ->
      if target = `Reach then
        LocalS (subst_projs_bform s f)
      else
        LocalS f
    | GlobalS f -> GlobalS (subst_projs target s f)

  let fv = function
    | LocalS  f -> fv_bform f
    | GlobalS f -> fv f

  let ty_fv = function
    | LocalS  f -> ty_fv_bform f
    | GlobalS f -> ty_fv f

  let get_terms = function
    | LocalS f -> f.formula::(Option.to_list f.bound)
    | GlobalS f -> get_terms f

  let project p = function
    | LocalS f -> LocalS (proj_bform p f)
    | GlobalS f -> GlobalS (     project p f)
end

module Babel_statement = struct

  let convert (type a b) ?loc ~(src:a s_kind) ~(dst:b s_kind) (s : a) : b
    =
    match src,dst with
    (* Identity cases *)
    | Local_s,  Local_s  -> s
    | Global_s, Global_s -> s
    | Any_s,    Any_s    -> s

    (* Injections into [any_form] *)
    | Local_s,  Any_s -> LocalS s
    | Global_s, Any_s -> GlobalS s

    (* Inverses of the injections. *)
    | Any_s, Local_s ->
      begin match s with
        | GlobalS (Atom (Reach s)) -> s
        | LocalS s -> s
        | _ -> Tactics.soft_failure ?loc CannotConvert
      end

    | Any_s, Global_s ->
      begin match s with
        | GlobalS f -> f
        | LocalS f -> Atom (Reach f)
      end

    (* Conversions between local and global formulas. *)
    | Local_s,  Global_s -> Atom (Reach s)
    | Global_s, Local_s  ->
      begin match s with
        | Atom (Reach s) -> s
        | _ -> Tactics.soft_failure ?loc CannotConvert
      end

  let subst : type a. a s_kind -> Term.subst -> a -> a = function
    | Local_s  -> subst_bform
    | Global_s -> subst
    | Any_s    -> PreAny_statement.subst

  let subst_projs :
    type a. a s_kind -> [`Equiv | `Reach] -> (Term.proj * Term.proj) list -> a -> a
    =
    fun kind target s f ->
    match kind with
    | Local_s  ->                  subst_projs_bform        s f
    | Global_s ->                  subst_projs       target s f
    | Any_s    -> PreAny_statement.subst_projs       target s f

  let tsubst : type a. a s_kind -> Type.tsubst -> a -> a = function
    | Local_s  -> tsubst_bform
    | Global_s -> tsubst
    | Any_s    -> PreAny_statement.tsubst

  let fv : type a. a s_kind -> a -> Vars.Sv.t = function
    | Local_s  -> fv_bform
    | Global_s -> fv
    | Any_s    -> PreAny_statement.fv

  let get_terms : type a. a s_kind -> a -> Term.term list = function
    | Local_s  -> fun f -> f.formula::(Option.to_list f.bound)
    | Global_s -> get_terms
    | Any_s    -> PreAny_statement.get_terms

  let _pp : type a. a s_kind -> a formatter_p = function
    | Local_s  ->                  _pp_bform
    | Global_s ->                  _pp ?context:None
    | Any_s    -> PreAny_statement._pp ?context:None

  let pp     : type a. a s_kind -> a formatter = 
    fun k -> _pp k (default_ppe ~dbg:false ())

  let pp_dbg : type a. a s_kind -> a formatter = 
    fun k -> _pp k (default_ppe ~dbg:true ())

  let project : type a. a s_kind -> Term.proj list -> a -> a = function
    | Local_s  -> proj_bform
    | Global_s -> project
    | Any_s    -> PreAny_statement.project

end

module Any_statement = struct
  include PreAny_statement

  let convert_from k f =
    Babel_statement.convert ~src:k ~dst:Any_s f

  let convert_to ?loc k f =
    Babel_statement.convert ?loc ~dst:k ~src:Any_s f
end
