(** Equivalence formulas.  *)

open Utils
    
module Sv = Vars.Sv
module Mv = Vars.Mv

module SE = SystemExpr
  
(*------------------------------------------------------------------*)
(** {2 Equivalence} *)

type equiv = Term.term list

let pp_equiv ppf (l : equiv) =
  Fmt.pf ppf "@[%a@]"
    (Fmt.list ~sep:(fun ppf () -> Fmt.pf ppf ",@ ") Term.pp)
    l

let pp_equiv_numbered ppf (l : equiv) =
  List.iteri (fun i elem ->
      Fmt.pf ppf "%i: @[%a@]@;" i Term.pp elem
    ) l

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

let pp_atom fmt = function
  | Equiv e -> Fmt.pf fmt "equiv(%a)" pp_equiv e
  | Reach f -> Fmt.pf fmt "@[[%a]@]" Term.pp f

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
  | Quant of quant * Vars.var list * form
  | Atom  of atom
  | Impl  of form * form
  | And   of form * form
  | Or    of form * form

let toplevel_prec = 0
let quant_fixity = 5   , `NonAssoc
let impl_fixity  = 10  , `Infix `Right
let or_fixity    = 20  , `Infix `Right
let and_fixity   = 25  , `Infix `Right

(** Internal *)
let rec pp 
    ((outer,side) : ('b * fixity) * assoc)
    (fmt : Format.formatter)
  = function
  | Atom at -> pp_atom fmt at

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

  | Quant (bd, vs, f) ->
    let pp fmt () = 
      Fmt.pf fmt "@[<2>%a (@[%a@]),@ %a@]"
        pp_quant bd
        Vars.pp_typed_list vs
        (pp (quant_fixity, `Right)) f
    in
    maybe_paren ~outer ~side ~inner:(fst quant_fixity, `Prefix) pp fmt ()


let pp (fmt : Format.formatter) (f : form) : unit =
  pp ((toplevel_prec, `NoParens), `NonAssoc) fmt f

(*------------------------------------------------------------------*)
let mk_quant q evs f = match evs, f with
  | [], _ -> f
  | _, Quant (q, evs', f) -> Quant (q, evs @ evs', f)
  | _, _ -> Quant (q, evs, f)

let mk_forall = mk_quant ForAll
let mk_exists = mk_quant Exists

let mk_reach_atom f = Atom (Reach f)

(*------------------------------------------------------------------*)
(** {2 Map (does not recurse) } *)

(** Does not recurse.
    Applies to arguments of index atoms (see atom_map). *)
let tmap (func : form -> form) (t : form) : form =

  let rec tmap = function
    | Quant (q, vs, b) -> Quant (q, vs, func b)
    | Impl (f1, f2)    -> Impl (tmap f1, tmap f2)
    | And (f1, f2)     -> And (tmap f1, tmap f2)
    | Or (f1, f2)      -> Or (tmap f1, tmap f2)
    | Atom at          -> Atom at
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

let tfold : (form -> 'b -> 'b) -> form -> 'b -> 'b =
  fun f t v ->
  let vref : 'b ref = ref v in
  let fi e = vref := (f e !vref) in
  titer fi t;
  !vref

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
(** {2 Substitution} *)

(** Free variables. *)
let rec fv = function
  | Atom at -> fv_atom at
  | And  (f, f0)
  | Or   (f, f0)
  | Impl (f,f0) -> Sv.union (fv f) (fv f0)
  | Quant (_, evs, b) -> Sv.diff (fv b) (Sv.of_list evs)

let rec subst s (f : form) =
  if s = [] ||
     (Term.is_var_subst s &&
      Sv.disjoint (Term.subst_support s) (fv f))
  then f
  else
    match f with
    | Atom at -> Atom (subst_atom s at)

    | And  (f0, f) -> And  (subst s f0, subst s f)
    | Or   (f0, f) -> Or   (subst s f0, subst s f)
    | Impl (f0, f) -> Impl (subst s f0, subst s f)

    | Quant (_, [], f) -> subst s f
    | Quant (q, v :: evs, b) ->
      let v, s = Term.subst_binding v s in
      let f = subst s (Quant (q, evs,b)) in
      mk_quant q [v] f

let tsubst_atom (ts : Type.tsubst) (at : atom) =
  match at with
  | Reach t -> Reach (Term.tsubst ts t)
  | Equiv e -> Equiv (List.map (Term.tsubst ts) e)

(** Type substitution *)
let tsubst (ts : Type.tsubst) (t : form) =
  let rec tsubst = function
    | Quant (q, vs, f) -> Quant (q, List.map (Vars.tsubst ts) vs, tsubst f)
    | Atom at -> Atom (tsubst_atom ts at)
    | _ as term -> tmap tsubst term
  in

  tsubst t

(*------------------------------------------------------------------*)
(** {2 Smart constructors and destructors} *)
type _form = form

(* TODO: factorize with code in Term.ml ? *)
module Smart : Term.SmartFO with type form = _form = struct
  type form = _form

  let todo () = Tactics.soft_failure (Failure "not implemented")

  (** {3 Constructors} *)
  let mk_true  = Atom (Reach Term.mk_true)
  let mk_false = Atom (Reach Term.mk_false)

  let mk_not ?simpl f = todo ()

  let mk_and ?simpl f1 f2 = And (f1, f2)
  let rec mk_ands ?simpl forms = match forms with
    | [] -> mk_true
    | [f0] -> f0
    | f0 :: forms -> And (f0, mk_ands forms)

  let mk_or ?simpl f1 f2 = Or (f1, f2)
  let rec mk_ors ?simpl forms = match forms with
    | [] -> mk_false
    | [f0] -> f0
    | f0 :: forms -> Or (f0, mk_ors forms)

  let mk_impl ?simpl f1 f2 = Impl (f1, f2)
  let rec mk_impls ?simpl l f = match l with
    | [] -> f
    | f0 :: impls -> Impl (f0, mk_impls impls f)

  let mk_forall ?(simpl=false) l f =
    let l =
      if simpl then
        let fv = fv f in
        List.filter (fun v -> Sv.mem v fv) l
      else l
    in
    mk_forall l f

  let mk_exists ?(simpl=false) l f =
    let l =
      if simpl then
        let fv = fv f in
        List.filter (fun v -> Sv.mem v fv) l
      else l
    in
    mk_exists l f

  (*------------------------------------------------------------------*)
  let mk_eq  ?simpl f1 f2 = Atom (Reach (Term.Smart.mk_eq  ?simpl f1 f2))
  let mk_leq ?simpl f1 f2 = Atom (Reach (Term.Smart.mk_leq ?simpl f1 f2))
  let mk_geq ?simpl f1 f2 = Atom (Reach (Term.Smart.mk_geq ?simpl f1 f2))
  let mk_lt  ?simpl f1 f2 = Atom (Reach (Term.Smart.mk_lt  ?simpl f1 f2))
  let mk_gt  ?simpl f1 f2 = Atom (Reach (Term.Smart.mk_gt  ?simpl f1 f2))

  (*------------------------------------------------------------------*)
  (** {3 Destructors} *)

  let destr_quant q = function
    | Quant (q', es, f) when q = q' -> Some (es, f)

    | Atom (Reach f) when Term.is_pure_timestamp f && q = Exists ->
        begin match Term.Smart.destr_exists f with
          | Some (es,f) -> Some (es, Atom (Reach f))
          | None -> None
        end

    | Atom (Reach f) when q = ForAll ->
        begin match Term.Smart.destr_forall f with
          | Some (es,f) -> Some (es, Atom (Reach f))
          | None -> None
        end

    | _ -> None

  let destr_forall = destr_quant ForAll
  let destr_exists = destr_quant Exists

  (*------------------------------------------------------------------*)
  let destr_quant1 q = function
    | Quant (q', v :: es, f) when q = q' -> Some (v, mk_quant q es f)
    | Atom (Reach f) when Term.is_pure_timestamp f && q = Exists ->
        begin match Term.Smart.destr_exists1 f with
          | Some (es,f) -> Some (es, Atom (Reach f))
          | None -> None
        end

    (* For a local meta-formula f,
       (Forall x. [f]) is equivalent to [forall x. f]. *)
    | Atom (Reach f) when q = ForAll ->
      begin match Term.Smart.destr_forall1 f with
          | Some (es,f) -> Some (es, Atom (Reach f))
          | None -> None
        end

    | _ -> None

  let destr_forall1 = destr_quant1 ForAll
  let destr_exists1 = destr_quant1 Exists

  (*------------------------------------------------------------------*)
  let destr_false f = todo ()
  let destr_true  f = todo ()
  let destr_not   f = todo ()

  let destr_and = function
    | And (f1, f2) -> Some (f1, f2)
    | Atom (Reach f) ->
        begin match Term.Smart.destr_and f with
          | Some (f1,f2) -> Some (Atom (Reach f1), Atom (Reach f2))
          | None -> None
        end
    | _ -> None

  let destr_or = function
    | Or (f1, f2) -> Some (f1, f2)
    | Atom (Reach f) ->
       begin match Term.Smart.destr_or f with
         | Some (f1,f2) when
           Term.is_pure_timestamp f1 || Term.is_pure_timestamp f2 ->
             Some (Atom (Reach f1), Atom (Reach f2))
         | _ -> None
       end
    | _ -> None

  let destr_impl = function
    | Impl (f1, f2) -> Some (f1, f2)
    | Atom (Reach f) ->
       begin match Term.Smart.destr_impl f with
         | Some (f1,f2) when Term.is_pure_timestamp f1 ->
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

  let destr_ors i f = mk_destr_right destr_or i f

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
  let is_false f = todo ()
  let is_true  f = todo ()
  let is_zero  f = todo ()
  let is_not   f = false
  let is_and   f = destr_and  f <> None
  let is_or    f = destr_or   f <> None
  let is_impl  f = destr_impl f <> None

  let is_forall = function Quant (ForAll, _, _) -> true | _ -> false
  let is_exists = function
    | Quant (Exists, _, _) -> true
    | Atom (Reach f) ->
        Term.Smart.is_exists f &&
        Term.is_pure_timestamp f
    | _ -> false

  let is_eq  f = destr_eq  f <> None
  let is_neq f = destr_neq f <> None
  let is_leq f = destr_leq f <> None
  let is_lt  f = destr_lt  f <> None

  (*------------------------------------------------------------------*)
  let rec decompose_quant q = function
    | Quant (q', es, f) when q = q' ->
      let es', f = decompose_quant q f in
      es @ es', f

    (* For a local meta-formula f,
     * (Forall x. [f]) is equivalent to [forall x. f]. *)
    | Atom (Reach f) when q = ForAll ->
      let es,f = Term.Smart.decompose_forall f in
      es, Atom (Reach f)

    | _ as f -> [], f

  let decompose_forall = decompose_quant ForAll
  let decompose_exists = decompose_quant Exists

  (*------------------------------------------------------------------*)
  let decompose_ands  f = todo ()
  let decompose_ors   f = todo ()

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

(*------------------------------------------------------------------*)
(** {2 Generalized formulas} *)

type any_form = [`Equiv of form | `Reach of Term.term]

let pp_any_form fmt (f : any_form) =
  match f with
  | `Equiv e -> pp fmt e
  | `Reach f -> Term.pp fmt f

let any_to_reach (f : any_form) : Term.term =
  match f with
  | `Equiv _ -> assert false
  | `Reach f -> f

let any_to_equiv (f : any_form) : form =
  match f with
  | `Equiv f -> f
  | `Reach _ -> assert false

(*------------------------------------------------------------------*)
type local_form = Term.term
type global_form = form

type _ f_kind =
  | Local_t  : local_form f_kind
  | Global_t : global_form f_kind
  | Any_t    : any_form f_kind

(** Module Any without conversion functions. *)
module PreAny = struct
  type t = any_form
  let pp fmt = function
    | `Reach f -> Term.pp fmt f
    | `Equiv f ->      pp fmt f

  let subst s = function
    | `Reach f -> `Reach (Term.subst s f)
    | `Equiv f -> `Equiv (     subst s f)

  let tsubst s = function
    | `Reach f -> `Reach (Term.tsubst s f)
    | `Equiv f -> `Equiv (     tsubst s f)

  let fv = function
    | `Reach f -> Term.fv f
    | `Equiv f -> fv f

  let get_terms = function
    | `Reach f -> [f]
    | `Equiv f -> get_terms f

  let project p = function
    | `Reach f -> `Reach (Term.project p f)
    | `Equiv f -> `Equiv (     project p f)
end

module Babel = struct

  type mapper = {
    call : 'a. 'a f_kind -> 'a -> 'a
  }

  let convert :
    type a b. ?loc:Location.t ->
              src:(a f_kind) ->
              dst:(b f_kind) ->
              a -> b
    = fun ?loc ~src ~dst f ->
    match src,dst with
      (* Identity cases *)
      | Local_t,  Local_t  -> f
      | Global_t, Global_t -> f
      | Any_t,    Any_t    -> f

      (* Injections into [any_form] *)
      | Local_t,  Any_t -> `Reach f
      | Global_t, Any_t -> `Equiv f

      (* Inverses of the injections. *)
      | Any_t, Local_t ->
          begin match f with
            | `Reach f -> f
            | _ -> Tactics.soft_failure ?loc CannotConvert
          end

      | Any_t, Global_t ->
          begin match f with
            | `Equiv f -> f
            | `Reach f -> Atom (Reach f)
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

  module Smart : Term.SmartFO with type form = any_form = struct
    type form = any_form

    let mk_true  = `Reach Term.mk_true
    let mk_false = `Reach Term.mk_false

    let mk_not ?simpl f =
      match f with
        | `Reach f -> `Reach (Term.Smart.mk_not ?simpl f)
        | `Equiv f -> `Equiv (Smart.mk_not ?simpl f)

    let mk_and ?simpl f g =
      match f,g with
        | `Reach f, `Reach g -> `Reach (Term.Smart.mk_and ?simpl f g)
        | `Equiv f, `Equiv g -> `Equiv (Smart.mk_and ?simpl f g)
        | _ -> assert false

    let mk_or ?simpl f g =
      match f,g with
        | `Reach f, `Reach g -> `Reach (Term.Smart.mk_or ?simpl f g)
        | `Equiv f, `Equiv g -> `Equiv (Smart.mk_or ?simpl f g)
        | _ -> assert false

    let mk_impl ?simpl f g : any_form =
      match f,g with
        | `Reach f, `Reach g -> `Reach (Term.Smart.mk_impl ?simpl f g)
        | `Equiv f, `Equiv g -> `Equiv (Smart.mk_impl ?simpl f g)
        | _ -> assert false

    let mk_ands ?simpl = function
      | [] -> `Reach (Term.Smart.mk_ands ?simpl [])
      | (`Reach _ :: _) as l ->
          let l = List.map (function `Reach f -> f | _ -> assert false) l in
          `Reach (Term.Smart.mk_ands ?simpl l)
      | (`Equiv _ :: _) as l ->
          let l = List.map (function `Equiv f -> f | _ -> assert false) l in
          `Equiv (Smart.mk_ands ?simpl l)

    let mk_ors ?simpl = function
      | [] -> `Reach (Term.Smart.mk_ors ?simpl [])
      | (`Reach _ :: _) as l ->
          let l = List.map (function `Reach f -> f | _ -> assert false) l in
          `Reach (Term.Smart.mk_ors ?simpl l)
      | (`Equiv _ :: _) as l ->
          let l = List.map (function `Equiv f -> f | _ -> assert false) l in
          `Equiv (Smart.mk_ors ?simpl l)

    let mk_impls ?simpl l f = match l,f with
      | [],`Reach f -> `Reach (Term.Smart.mk_impls ?simpl [] f)
      | [],`Equiv f -> `Equiv (Smart.mk_impls ?simpl [] f)
      | (`Reach _ :: _) as l, `Reach f ->
          let l = List.map (function `Reach f -> f | _ -> assert false) l in
          `Reach (Term.Smart.mk_impls ?simpl l f)
      | (`Equiv _ :: _) as l, `Equiv f ->
          let l = List.map (function `Equiv f -> f | _ -> assert false) l in
          `Equiv (Smart.mk_impls ?simpl l f)
      | _ -> assert false

    let mk_eq  ?simpl f g = `Reach (Term.Smart.mk_eq  ?simpl f g)
    let mk_leq ?simpl f g = `Reach (Term.Smart.mk_leq ?simpl f g)
    let mk_geq ?simpl f g = `Reach (Term.Smart.mk_geq ?simpl f g)
    let mk_lt  ?simpl f g = `Reach (Term.Smart.mk_lt  ?simpl f g)
    let mk_gt  ?simpl f g = `Reach (Term.Smart.mk_gt  ?simpl f g)

    (*------------------------------------------------------------------*)
    let mk_forall ?simpl vs = function
      | `Reach f -> `Reach (Term. Smart.mk_forall ?simpl vs f)
      | `Equiv f -> `Equiv (      Smart.mk_forall ?simpl vs f)

    let mk_exists ?simpl vs = function
      | `Reach f -> `Reach (Term. Smart.mk_exists ?simpl vs f)
      | `Equiv f -> `Equiv (      Smart.mk_exists ?simpl vs f)

    let destr_forall1 = function
      | `Reach f -> omap (fun (vs,f) -> vs,`Reach f) (Term. Smart.destr_forall1 f)
      | `Equiv f -> omap (fun (vs,f) -> vs,`Equiv f) (      Smart.destr_forall1 f)

    let destr_exists1 = function
      | `Reach f -> omap (fun (vs,f) -> vs,`Reach f) (Term. Smart.destr_exists1 f)
      | `Equiv f -> omap (fun (vs,f) -> vs,`Equiv f) (      Smart.destr_exists1 f)

    let destr_forall = function
      | `Reach f -> omap (fun (vs,f) -> vs,`Reach f) (Term. Smart.destr_forall f)
      | `Equiv f -> omap (fun (vs,f) -> vs,`Equiv f) (      Smart.destr_forall f)

    let destr_exists = function
      | `Reach f -> omap (fun (vs,f) -> vs,`Reach f) (Term. Smart.destr_exists f)
      | `Equiv f -> omap (fun (vs,f) -> vs,`Equiv f) (      Smart.destr_exists f)

    (*------------------------------------------------------------------*)
    let destr_false = function
      | `Reach f -> Term.Smart.destr_false f
      | `Equiv f -> Smart.destr_false f

    let destr_true = function
      | `Reach f -> Term.Smart.destr_true f
      | `Equiv f -> Smart.destr_true f

    let destr_not = function
      | `Reach f -> omap (fun f -> `Reach f) (Term.Smart.destr_not f)
      | `Equiv f -> omap (fun f -> `Equiv f) (Smart.destr_not f)

    let destr_and = function
      | `Reach f ->
          omap (fun (x,y) -> `Reach x, `Reach y) (Term.Smart.destr_and f)
      | `Equiv f ->
          omap (fun (x,y) -> `Equiv x, `Equiv y) (Smart.destr_and f)
    let destr_or = function
      | `Reach f ->
          omap (fun (x,y) -> `Reach x, `Reach y) (Term.Smart.destr_or f)
      | `Equiv f ->
          omap (fun (x,y) -> `Equiv x, `Equiv y) (Smart.destr_or f)
    let destr_impl = function
      | `Reach f ->
          omap (fun (x,y) -> `Reach x, `Reach y) (Term.Smart.destr_impl f)
      | `Equiv f ->
          omap (fun (x,y) -> `Equiv x, `Equiv y) (Smart.destr_impl f)

    (*------------------------------------------------------------------*)
    let is_false = function
      | `Reach f -> Term.Smart.is_false f
      | `Equiv f ->      Smart.is_false f

    let is_true = function
      | `Reach f -> Term.Smart.is_true f
      | `Equiv f ->      Smart.is_true f

    let is_zero = function
      | `Reach f -> Term.Smart.is_zero f
      | `Equiv f ->      Smart.is_zero f

    let is_not = function
      | `Reach f -> Term.Smart.is_not f
      | `Equiv f ->      Smart.is_not f

    let is_and = function
      | `Reach f -> Term.Smart.is_and f
      | `Equiv f ->      Smart.is_and f

    let is_or = function
      | `Reach f -> Term.Smart.is_or f
      | `Equiv f ->      Smart.is_or f

    let is_impl = function
      | `Reach f -> Term.Smart.is_impl f
      | `Equiv f ->      Smart.is_impl f

    let is_forall = function
      | `Reach f -> Term.Smart.is_forall f
      | `Equiv f ->      Smart.is_forall f

    let is_exists = function
      | `Reach f -> Term.Smart.is_exists f
      | `Equiv f ->      Smart.is_exists f

    let is_eq = function
      | `Reach f -> Term.Smart.is_eq f
      | `Equiv f ->      Smart.is_eq f

    let is_neq = function
      | `Reach f -> Term.Smart.is_neq f
      | `Equiv f ->      Smart.is_neq f

    let is_leq = function
      | `Reach f -> Term.Smart.is_leq f
      | `Equiv f ->      Smart.is_leq f

    let is_lt = function
      | `Reach f -> Term.Smart.is_lt f
      | `Equiv f ->      Smart.is_lt f

    (*------------------------------------------------------------------*)
    let destr_ands i = function
      | `Reach f ->
          omap (fun l -> List.map (fun x -> `Reach x) l)
            (Term.Smart.destr_ands i f)
      | `Equiv f ->
          omap (fun l -> List.map (fun x -> `Equiv x) l)
            (Smart.destr_ands i f)

    let destr_ors i = function
      | `Reach f ->
          omap (fun l -> List.map (fun x -> `Reach x) l)
            (Term.Smart.destr_ors i f)
      | `Equiv f ->
          omap (fun l -> List.map (fun x -> `Equiv x) l)
            (Smart.destr_ors i f)

    let destr_impls i = function
      | `Reach f ->
          omap (fun l -> List.map (fun x -> `Reach x) l)
            (Term.Smart.destr_impls i f)
      | `Equiv f ->
          omap (fun l -> List.map (fun x -> `Equiv x) l)
            (Smart.destr_impls i f)

    let destr_eq = function
      | `Reach f -> Term.Smart.destr_eq f
      | `Equiv f ->      Smart.destr_eq f

    let destr_neq = function
      | `Reach f -> Term.Smart.destr_neq f
      | `Equiv f ->      Smart.destr_neq f

    let destr_leq = function
      | `Reach f -> Term.Smart.destr_leq f
      | `Equiv f ->      Smart.destr_leq f

    let destr_lt = function
      | `Reach f -> Term.Smart.destr_lt f
      | `Equiv f ->      Smart.destr_lt f

    (*------------------------------------------------------------------*)
    let decompose_forall = function
      | `Reach f ->
          let vs,f = Term.Smart.decompose_forall f in
            vs, `Reach f
      | `Equiv f ->
          let vs,f = Smart.decompose_forall f in
            vs, `Equiv f

    let decompose_exists = function
      | `Reach f ->
          let vs,f = Term.Smart.decompose_exists f in
            vs, `Reach f
      | `Equiv f ->
          let vs,f = Smart.decompose_exists f in
            vs, `Equiv f

    let decompose_ands = function
      | `Reach f -> List.map (fun x -> `Reach x) (Term.Smart.decompose_ands f)
      | `Equiv f -> List.map (fun x -> `Equiv x) (     Smart.decompose_ands f)

    let decompose_ors = function
      | `Reach f -> List.map (fun x -> `Reach x) (Term.Smart.decompose_ors f)
      | `Equiv f -> List.map (fun x -> `Equiv x) (     Smart.decompose_ors f)

    let decompose_impls = function
      | `Reach f -> List.map (fun x -> `Reach x) (Term.Smart.decompose_impls f)
      | `Equiv f -> List.map (fun x -> `Equiv x) (     Smart.decompose_impls f)

    let decompose_impls_last = function
      | `Reach f ->
          let l,f = Term.Smart.decompose_impls_last f in
            List.map (fun x -> `Reach x) l, `Reach f
      | `Equiv f ->
          let l,f = Smart.decompose_impls_last f in
            List.map (fun x -> `Equiv x) l, `Equiv f
  end

end
