(** Equivalence formulas.  *)

open Utils
    
module Sv = Vars.Sv
module Mv = Vars.Mv

module SE = SystemExpr
  
(*------------------------------------------------------------------*)
(** {2 Equivalence} *)

type equiv = Term.term list

(*------------------------------------------------------------------*)
let _pp_equiv ~dbg ppf (l : equiv) =
  Fmt.pf ppf "@[%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") (Term._pp ~dbg))
    l

let pp_equiv = _pp_equiv ~dbg:false

(*------------------------------------------------------------------*)
let _pp_equiv_numbered ~dbg ppf (l : equiv) =
  List.iteri (fun i elem ->
      Fmt.pf ppf "%i: @[%a@]@;" i (Term._pp ~dbg) elem
    ) l

let pp_equiv_numbered = _pp_equiv_numbered ~dbg:false

(*------------------------------------------------------------------*)
let subst_equiv (subst : Term.subst) (e : equiv) : equiv =
  List.map (Term.subst subst) e

(** Free variables of an [equiv]. *)
let fv_equiv e : Sv.t =
  List.fold_left (fun sv elem ->
      Sv.union sv (Term.fv elem)
    ) Sv.empty e

(*------------------------------------------------------------------*)
(** {2 Equivalence atoms} *)

type atom =
  | Equiv of equiv
  (** Equiv u corresponds to (u)^left ~ (u)^right *)

  | Reach of Term.term
  (** Reach(φ) corresponds to (φ)^left ~ ⊤ ∧ (φ)^right ~ ⊤ *)

(*------------------------------------------------------------------*)
let _pp_atom ~dbg fmt = function
  | Equiv e -> Fmt.pf fmt "equiv(%a)" (_pp_equiv ~dbg) e
  | Reach f -> 
    Fmt.pf fmt "@[[%a]@]" (Term._pp ~dbg) f

let pp_atom = _pp_atom ~dbg:false

(*------------------------------------------------------------------*)
let subst_atom (subst : Term.subst) (a : atom) : atom =
  match a with
  | Equiv e -> Equiv (subst_equiv subst e)
  | Reach f -> Reach (Term.subst subst f)


(** Free variables of an [atom]. *)
let fv_atom = function
  | Equiv e -> fv_equiv e
  | Reach f -> Term.fv f

(*------------------------------------------------------------------*)
(** {2 Equivalence formulas} *)
(** We only support a small fragment for now *)

type quant = ForAll | Exists

let pp_quant fmt = function
  | ForAll -> Fmt.pf fmt "Forall"
  | Exists -> Fmt.pf fmt "Exists"

type form =
  | Quant of quant * Vars.tagged_vars * form
  | Atom  of atom
  | Impl  of form * form
  | And   of form * form
  | Or    of form * form

(*------------------------------------------------------------------*)
(** Free variables. *)
let rec fv = function
  | Atom at -> fv_atom at
  | And  (f, f0)
  | Or   (f, f0)
  | Impl (f,f0) -> Sv.union (fv f) (fv f0)
  | Quant (_, evs, b) -> Sv.diff (fv b) (Sv.of_list (List.map fst evs))

(*------------------------------------------------------------------*)
let mk_quant0_tagged q (evs : Vars.tagged_vars) f = match evs, f with
  | [], _ -> f
  | _, Quant (q', evs', f) when q = q' -> Quant (q, evs @ evs', f)
  | _, _ -> Quant (q, evs, f)

let%test_unit _ =
  let f = Atom (Equiv []) in
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

let mk_reach_atom f = Atom (Reach f)
let mk_equiv_atom f = Atom (Equiv f)

(*------------------------------------------------------------------*)
(** {2 Map (does not recurse) } *)

(** Does not recurse. *)
let tmap (func : form -> form) (t : form) : form =

  let tmap = function
    | Quant (q, vs, b) -> Quant (q, vs, func b)

    | Impl (f1, f2) -> Impl (func f1, func f2)
    | And  (f1, f2) -> And  (func f1, func f2)
    | Or   (f1, f2) -> Or   (func f1, func f2)

    | Atom at       -> Atom at
  in
  tmap t

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

    | _ -> tmap (subst s) f

(*------------------------------------------------------------------*)
(** Projection substitution *)

let subst_projs_atom (s : (Term.proj * Term.proj) list) (at : atom) : atom =
  match at with
  | Reach t -> Reach (Term.subst_projs s t)
  | Equiv e -> Equiv (List.map (Term.subst_projs s) e)

let subst_projs (s : (Term.proj * Term.proj) list) (t : form) : form =
  let rec doit = function
    | Atom at -> Atom (subst_projs_atom s at)
    | _ as term -> tmap doit term
  in

  doit t

(*------------------------------------------------------------------*)
(** Type substitutions *)

let tsubst_atom (ts : Type.tsubst) (at : atom) =
  match at with
  | Reach t -> Reach (Term.tsubst ts t)
  | Equiv e -> Equiv (List.map (Term.tsubst ts) e)

let tsubst (ts : Type.tsubst) (t : form) =
  let rec tsubst = function
    | Quant (q, vs, f) -> Quant (q, List.map (fst_bind (Vars.tsubst ts)) vs, tsubst f)
    | Atom at -> Atom (tsubst_atom ts at)
    | _ as term -> tmap tsubst term
  in

  tsubst t

(*------------------------------------------------------------------*)
(** {2 Pretty printing} *)

let toplevel_prec = 0
let quant_fixity = 5   , `NonAssoc
let impl_fixity  = 10  , `Infix `Right
let or_fixity    = 20  , `Infix `Right
let and_fixity   = 25  , `Infix `Right

(** Internal *)
let pp ~(dbg:bool) = 
  let rec pp 
      ((outer,side) : ('b * fixity) * assoc)
      (fmt : Format.formatter)
    = function
      | Atom at -> _pp_atom ~dbg fmt at

      | Impl (f0, f) ->
        let pp fmt () = 
          Fmt.pf fmt "@[<0>%a ->@ %a@]"
            (pp (impl_fixity, `Left)) f0 
            (pp (impl_fixity, `Right)) f
        in
        maybe_paren ~outer ~side ~inner:impl_fixity pp fmt ()

      | And (f0, f) ->
        let pp fmt () =     
          Fmt.pf fmt "@[<0>%a /\\@ %a@]" 
            (pp (and_fixity, `Left)) f0 
            (pp (and_fixity, `Right)) f
        in
        maybe_paren ~outer ~side ~inner:and_fixity pp fmt ()

      | Or (f0, f) ->
        let pp fmt () = 
          Fmt.pf fmt "@[<0>%a \\/@ %a@]"
            (pp (or_fixity, `Left)) f0 
            (pp (or_fixity, `Right)) f
        in
        maybe_paren ~outer ~side ~inner:or_fixity pp fmt ()

      | Quant (bd, vs0, f) ->
        let _, vs, s = (* rename quantified vars. to avoid name clashes *)
          let fv_f = List.fold_left ((^~) (fst_map Sv.remove)) (fv f) vs0 in
          Term.add_vars_simpl_env (Vars.of_set fv_f) (List.map fst vs0)
        in
        let f = subst s f in

        let pp fmt () = 
          Fmt.pf fmt "@[<2>%a (@[%a@]),@ %a@]"
            pp_quant bd
            (Vars._pp_typed_tagged_list ~dbg)
            (List.map2 (fun v (_, tag) -> v,tag) vs vs0)
            (pp (quant_fixity, `Right)) f
        in
        maybe_paren ~outer ~side ~inner:(fst quant_fixity, `Prefix) pp fmt ()
  in
  pp

let pp_toplevel ~dbg (fmt : Format.formatter) (f : form) : unit =
  pp ~dbg ((toplevel_prec, `NoParens), `NonAssoc) fmt f
    
(** Exported *)
let _pp    = pp_toplevel
let pp     = pp_toplevel ~dbg:false
let pp_dbg = pp_toplevel ~dbg:true

(*------------------------------------------------------------------*)
(** {2 Misc} *)

let is_constant ?(env : Env.t option) (t : Term.term) : bool =
  let env = odflt (Env.init ~table:Symbols.builtins_table ()) env in
  HighTerm.is_constant env t

let is_system_indep
    ?(env : Env.t = Env.init ~table:Symbols.builtins_table ())
    (t    : Term.term)
  : bool
  =
  HighTerm.is_system_indep env t

let rec get_terms = function
  | Atom (Reach f) -> [f]
  | Atom (Equiv e) -> e
  | And  (e1, e2)
  | Or   (e1, e2)
  | Impl (e1, e2) -> get_terms e1 @ get_terms e2
  | Quant _ -> []

(*------------------------------------------------------------------*)
let rec project (projs : Term.proj list) (f : form) : form =
  match f with
  | Atom (Reach f) -> Atom (Reach (Term.project projs f))

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
  let mk_true  = Atom (Reach Term.mk_true)
  let mk_false = Atom (Reach Term.mk_false)

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
  let mk_eq  ?simpl f1 f2 = Atom (Reach (Term.Smart.mk_eq  ?simpl f1 f2))
  let mk_neq ?simpl f1 f2 = Atom (Reach (Term.Smart.mk_neq ?simpl f1 f2))
  let mk_leq        f1 f2 = Atom (Reach (Term.Smart.mk_leq        f1 f2))
  let mk_geq        f1 f2 = Atom (Reach (Term.Smart.mk_geq        f1 f2))
  let mk_lt  ?simpl f1 f2 = Atom (Reach (Term.Smart.mk_lt  ?simpl f1 f2))
  let mk_gt  ?simpl f1 f2 = Atom (Reach (Term.Smart.mk_gt  ?simpl f1 f2))

  (*------------------------------------------------------------------*)
  (** {3 Destructors} *)

  let destr_quant_tagged ?env q = function
    | Quant (q', es, f) when q = q' -> Some (es, f)

    (* case [f = ∃es. f0], check that:
       - [f] is constant
       - [f0] is system-independant *)
    | Atom (Reach f) when q = Exists && is_constant ?env f ->
        begin match Term.Smart.destr_exists_tagged f with
          | Some (es,f0) when is_system_indep ?env f0 ->
            Some (es, Atom (Reach f0))
          | _ -> None
        end

    | Atom (Reach f) when q = ForAll ->
        begin match Term.Smart.destr_forall_tagged f with
          | Some (es,f) -> Some (es, Atom (Reach f))
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
    | Atom (Reach f) when q = Exists && is_constant ?env f ->
        begin match Term.Smart.destr_exists1_tagged f with
          | Some (es,f0) when is_system_indep ?env f0 ->
            Some (es, Atom (Reach f0))
          | _ -> None
        end

    (* For a local meta-formula f,
       (Forall x. [f]) is equivalent to [forall x. f]. *)
    | Atom (Reach f) when q = ForAll ->
      begin match Term.Smart.destr_forall1_tagged f with
          | Some (es,f) -> Some (es, Atom (Reach f))
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
  let destr_false _f = todo ()
  let destr_true  _f = todo ()
  let destr_not   _f = todo ()

  let destr_and = function
    | And (f1, f2) -> Some (f1, f2)
    | Atom (Reach f) ->
        begin match Term.Smart.destr_and f with
          | Some (f1,f2) -> Some (Atom (Reach f1), Atom (Reach f2))
          | None -> None
        end
    | _ -> None

  let destr_or ?env = function
    | Or (f1, f2) -> Some (f1, f2)
    | Atom (Reach f) ->
       begin match Term.Smart.destr_or f with
         | Some (f1,f2) when
             (is_constant ?env f1 && is_system_indep ?env f1) ||
             (is_constant ?env f2 && is_system_indep ?env f2)
           ->
             Some (Atom (Reach f1), Atom (Reach f2))
         | _ -> None
       end
    | _ -> None

  let destr_impl ?env = function
    | Impl (f1, f2) -> Some (f1, f2)
    | Atom (Reach f) ->
       begin match Term.Smart.destr_impl f with
         | Some (f1,f2) when
             is_constant ?env f1 && is_system_indep ?env f1 ->
             Some (Atom (Reach f1), Atom (Reach f2))
         | _ -> None
       end
    | _ -> None

  let destr_iff = function
    | Atom (Reach f) ->
       begin match Term.Smart.destr_iff f with
         | Some (f1,f2) ->
             Some (Atom (Reach f1), Atom (Reach f2))
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

  let destr_eq = function
    | Atom (Reach f) -> Term.destr_eq f
    | _ -> None

  let destr_neq = function
    | Atom (Reach f) -> Term.destr_eq f
    | _ -> None

  let destr_leq = function
    | Atom (Reach f) -> Term.destr_eq f
    | _ -> None

  let destr_lt = function
    | Atom (Reach f) -> Term.destr_eq f
    | _ -> None

  (*------------------------------------------------------------------*)
  let is_false _f = todo ()
  let is_true  _f = todo ()
  let is_zero  _f = todo ()
  let is_not   _f = false       (* FIXME *)
  let is_and   f     = destr_and       f <> None
  let is_or   ?env f = destr_or   ?env f <> None
  let is_impl ?env f = destr_impl ?env f <> None
  let is_iff   f     = destr_iff       f <> None

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
    | Atom (Reach f) when q = ForAll ->
      let es,f = Term.Smart.decompose_forall_tagged f in
      es, Atom (Reach f)

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
  let decompose_ands _f = todo ()
  let decompose_ors  _f = todo ()

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
  | Atom (Equiv e) -> Some e
  | _ -> None

let is_equiv f = destr_equiv f <> None

(*------------------------------------------------------------------*)
(** {2 Generalized formulas} *)

type any_form = Global of form | Local of Term.term

let pp_any_form fmt (f : any_form) =
  match f with
  | Global e -> pp fmt e
  | Local f -> Term.pp fmt f

let any_to_reach (f : any_form) : Term.term =
  match f with
  | Global _ -> assert false
  | Local f -> f

let any_to_equiv (f : any_form) : form =
  match f with
  | Global f -> f
  | Local _ -> assert false

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

  let _pp ~dbg fmt = function
    | Local  f -> Term._pp ~dbg fmt f
    | Global f ->      _pp ~dbg fmt f

  let pp_dbg fmt = function
    | Local  f -> Term.pp_dbg fmt f
    | Global f ->      pp_dbg fmt f

  let subst s = function
    | Local  f -> Local  (Term.subst s f)
    | Global f -> Global (     subst s f)

  let tsubst s = function
    | Local  f -> Local  (Term.tsubst s f)
    | Global f -> Global (     tsubst s f)

  let subst_projs s = function
    | Local  f -> Local  (Term.subst_projs s f)
    | Global f -> Global (     subst_projs s f)

  let fv = function
    | Local  f -> Term.fv f
    | Global f -> fv f

  let get_terms = function
    | Local  f -> [f]
    | Global f -> get_terms f

  let project p = function
    | Local  f -> Local  (Term.project p f)
    | Global f -> Global (     project p f)
end

module Babel = struct

  type mapper = {
    call : 'a. 'a f_kind -> 'a -> 'a
  }

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
          | Global (Atom (Reach f)) -> f
          | Local f -> f
          | _ -> Tactics.soft_failure ?loc CannotConvert
        end

      | Any_t, Global_t ->
        begin match f with
          | Global f -> f
          | Local f -> Atom (Reach f)
        end

      (* Conversions between local and global formulas. *)
      | Local_t,  Global_t -> Atom (Reach f)
      | Global_t, Local_t  ->
        begin match f with
          | Atom (Reach f) -> f
          | _ -> Tactics.soft_failure ?loc CannotConvert
        end

  let subst : type a. a f_kind -> Term.subst -> a -> a = function
    | Local_t  -> Term.subst
    | Global_t -> subst
    | Any_t    -> PreAny.subst

  let subst_projs 
    : type a. a f_kind -> (Term.proj * Term.proj) list -> a -> a 
    = function
      | Local_t  -> Term.subst_projs
      | Global_t -> subst_projs
      | Any_t    -> PreAny.subst_projs

  let tsubst : type a. a f_kind -> Type.tsubst -> a -> a = function
    | Local_t  -> Term.tsubst
    | Global_t -> tsubst
    | Any_t    -> PreAny.tsubst

  let fv : type a. a f_kind -> a -> Vars.Sv.t = function
    | Local_t  -> Term.fv
    | Global_t -> fv
    | Any_t    -> PreAny.fv

  let term_get_terms x = [x]

  let get_terms : type a. a f_kind -> a -> Term.term list = function
    | Local_t  -> term_get_terms
    | Global_t -> get_terms
    | Any_t    -> PreAny.get_terms

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
        | Local f -> Local (Term.Smart.mk_not ?simpl f)
        | Global f -> Global (Smart.mk_not ?simpl f)

    let mk_and ?simpl f g =
      match f,g with
        | Local f, Local g -> Local (Term.Smart.mk_and ?simpl f g)
        | Global f, Global g -> Global (Smart.mk_and ?simpl f g)
        | _ -> assert false

    let mk_or ?simpl f g =
      match f,g with
        | Local f, Local g -> Local (Term.Smart.mk_or ?simpl f g)
        | Global f, Global g -> Global (Smart.mk_or ?simpl f g)
        | _ -> assert false

    let mk_impl ?simpl f g : any_form =
      match f,g with
        | Local f, Local g -> Local (Term.Smart.mk_impl ?simpl f g)
        | Global f, Global g -> Global (Smart.mk_impl ?simpl f g)
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
      | [],Local f -> Local (Term.Smart.mk_impls ?simpl [] f)
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
    let mk_geq        f g = Local (Term.Smart.mk_geq        f g)
    let mk_lt  ?simpl f g = Local (Term.Smart.mk_lt  ?simpl f g)
    let mk_gt  ?simpl f g = Local (Term.Smart.mk_gt  ?simpl f g)

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
      | Local  f ->
        omap (fun (vs,f) -> vs, Local  f) (Term.Smart.destr_exists1_tagged      f)
      | Global f ->
        omap (fun (vs,f) -> vs, Global f) (     Smart.destr_exists1_tagged ?env f)

    let destr_forall_tagged = function
      | Local  f -> omap (fun (vs,f) -> vs, Local  f) (Term.Smart.destr_forall_tagged f)
      | Global f -> omap (fun (vs,f) -> vs, Global f) (     Smart.destr_forall_tagged f)

    let destr_exists_tagged ?env = function
      | Local  f ->
        omap (fun (vs,f) -> vs, Local  f) (Term.Smart.destr_exists_tagged      f)
      | Global f ->
        omap (fun (vs,f) -> vs, Global f) (     Smart.destr_exists_tagged ?env f)
                      
    (*------------------------------------------------------------------*)
    let destr_false = function
      | Local  f -> Term.Smart.destr_false f
      | Global f ->      Smart.destr_false f

    let destr_true = function
      | Local  f -> Term.Smart.destr_true f
      | Global f ->      Smart.destr_true f

    let destr_not = function
      | Local  f -> omap (fun f -> Local f)  (Term.Smart.destr_not f)
      | Global f -> omap (fun f -> Global f) (     Smart.destr_not f)

    let destr_and = function
      | Local f ->
          omap (fun (x,y) -> Local x, Local y)   (Term.Smart.destr_and f)
      | Global f ->
          omap (fun (x,y) -> Global x, Global y) (     Smart.destr_and f)

    let destr_or ?env = function
      | Local f ->
          omap (fun (x,y) -> Local x, Local y)   (Term.Smart.destr_or      f)
      | Global f ->
          omap (fun (x,y) -> Global x, Global y) (     Smart.destr_or ?env f)

    let destr_impl ?env = function
      | Local f ->
          omap (fun (x,y) -> Local x, Local y) (Term.Smart.destr_impl f)
      | Global f ->
          omap (fun (x,y) -> Global x, Global y) (Smart.destr_impl ?env f)

    let destr_iff =  function
      | Local f ->
          omap (fun (x,y) -> Local x, Local y) (Term.Smart.destr_iff f)
      | Global f ->
          omap (fun (x,y) -> Global x, Global y) (Smart.destr_iff f)


    (*------------------------------------------------------------------*)
    let is_false = function
      | Local  f -> Term.Smart.is_false f
      | Global f ->      Smart.is_false f

    let is_true = function
      | Local  f -> Term.Smart.is_true f
      | Global f ->      Smart.is_true f

    let is_zero = function
      | Local  f -> Term.Smart.is_zero f
      | Global f ->      Smart.is_zero f

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
      | Local  f -> List.map (fun x -> Local x ) (Term.Smart.decompose_ands f)
      | Global f -> List.map (fun x -> Global x) (     Smart.decompose_ands f)

    let decompose_ors = function
      | Local  f -> List.map (fun x -> Local x ) (Term.Smart.decompose_ors f)
      | Global f -> List.map (fun x -> Global x) (     Smart.decompose_ors f)

    let decompose_impls = function
      | Local  f -> List.map (fun x -> Local x ) (Term.Smart.decompose_impls f)
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
