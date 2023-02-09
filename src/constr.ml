module SE = SystemExpr

module Mt = Term.Mt
module Mv = Vars.Mv
              
(*------------------------------------------------------------------*)
(** - Huet's unification algorithm using union-find.
     See "Unification: A Multidisciplinary Survey" by Kevin Knight.

    - Note that there is difficulty in the handling of names, which is not
    standard. Basically, they should behave as function symbols that dont have
    to be unified, except with other names.

    - Also, note that during the unification and graph-based inequality
    constraints solving, the union-find structure contains an
    *under-approximation* of equality equivalence classes. *)

open Graph
open Utils

module L = Location

(*------------------------------------------------------------------*)
let dbg s = Printer.prt (if Config.debug_constr () then `Dbg else `Ignore) s

(*------------------------------------------------------------------*)
(** Stateful memoization for conversion of [Term.term] to [Vars.var],
    which are then used to build a [ut] *)
type memo = { 
  mutable memo : Vars.var Mt.t;     (** Memoized results *)
  mutable rev  : Term.term Mv.t     (** Reversed map *)
}

let mk_memo () : memo =
  { memo = Mt.empty; rev = Mv.empty; }
  
(*------------------------------------------------------------------*)
exception Unsupported

module Utv : sig
  type ut = { hash : int;
              cnt  : ut_cnt }

  and ut_cnt = private
    | UVar  of Vars.var
    | UPred of ut
    | UName of Symbols.action * ut list
    | UInit
    | UUndef                    (* (x <> UUndef) iff. (Happens x) *)

  val uname  : Symbols.action -> ut list -> ut
  val upred  : ut -> ut
  val uinit  : ut
  val uundef : ut

  val term_to_ut : memo -> Term.term -> ut
  val ut_to_term : memo -> ut -> Term.term

  module Ut : Hashtbl.HashedType with type t = ut

end = struct
  type ut = { hash : int;
              cnt  : ut_cnt; }

  and ut_cnt =
    | UVar  of Vars.var
    | UPred of ut
    | UName of Symbols.action * ut list
    | UInit
    | UUndef

  (** Hash-consing.
      In [hash] and [equal], we can assume that strit subterms
      are properly hash-consed (but not the term itself). *)
  module Ut = struct
    type t = ut

    let hash t = match t.cnt with
      | UPred t' -> Utils.hcombine 0 t'.hash
      | UInit -> 1
      | UUndef -> 2
      | UVar uv -> Utils.hcombine 3 (Hashtbl.hash uv)
      | UName (a,ts) ->
        Utils.hcombine_list (fun x -> x.hash) (Hashtbl.hash a) ts

    let equal t t' = match t.cnt, t'.cnt with
      | UPred t, UPred t' -> t.hash = t'.hash
      | UInit, UInit
      | UUndef, UUndef -> true
      | UVar uv, UVar uv' -> uv = uv'
      | UName (a,ts), UName (a',ts') ->
        a = a' &&
        List.for_all2 (fun x y -> x.hash = y.hash) ts ts'
      | _ -> false

  end
  module Hut = Ephemeron.K1.Make(Ut)

  let hcons_cpt = ref 0
  let ht = Hut.create 256

  let make cnt =
    let ut = { hash = !hcons_cpt ; cnt = cnt } in
    try Hut.find ht ut with
    | Not_found ->
      incr hcons_cpt;
      Hut.add ht ut ut;
      ut

  let uvar v = UVar v |> make

  let uname a us = UName (a, us) |> make

  let uinit = UInit |> make

  let uundef = UUndef |> make

  let upred u =
    if u.cnt = UInit || u.cnt = UUndef then uundef
    else UPred u |> make

  (*------------------------------------------------------------------*)
  (** Box a term. 
      Uses memoization: convertible terms are boxed identically. *)
  let box_term (memo : memo) (t : Term.term) : ut = 
    let found = ref None in
    Mt.iter (fun t' res ->
        if Term.equal t t' then found := Some res
      ) memo.memo;
    match !found with
    | None ->
      let v = Vars.make_fresh (Term.ty t) "x" in
      memo.memo <- Mt.add t v memo.memo;
      memo.rev  <- Mv.add v t memo.rev;

      uvar v
    | Some v -> uvar v

  (*------------------------------------------------------------------*)
  let term_to_ut (memo : memo) (ts : Term.term) : ut =
    let rec doit = function
      | Term.Var tv -> uvar tv
      | Term.Fun (fs, _, [ts]) when fs = Term.f_pred -> upred (doit ts)
      | Term.Action (s,_) when s = Symbols.init_action -> uinit
      | Term.Action (s,l) -> uname s (List.map doit l)

      (* For arbitrary term, we use [box_term], which createa a fresh
         variable and associate it to [t] (with memoisation).
         We log this association to revert it later. *)
      | t -> box_term memo t
    in
    doit ts
      
  let ut_to_term (memo : memo) (ut : ut) : Term.term =
    let rec doit t =
      match t.cnt with
      | UVar v ->
        (* revert the logged association if necessary *)
        Mv.find_dflt (Term.mk_var v) v memo.rev

      | UName (a, is) ->
        Term.mk_action a (List.map doit is)

      | UPred ut -> Term.mk_pred (doit ut)
      | UInit  -> Term.init
      | UUndef -> assert false
    in
    doit ut
      
end

open Utv

let pp_uvar = Vars.pp_dbg

let rec pp_ut_cnt ppf = function
  | UVar uv  -> pp_uvar ppf uv
  | UPred ts -> Fmt.pf ppf "@[<hov>pred(%a)@]" pp_ut_cnt ts.cnt
  | UName (a,is) ->
    Fmt.pf ppf "@[%a[%a]@]"
      Fmt.string (Symbols.to_string a)
      (Fmt.list ~sep:Fmt.comma pp_ut_cnt) (List.map (fun x -> x.cnt) is)
  | UInit  -> Fmt.pf ppf "init"
  | UUndef -> Fmt.pf ppf "⊥"

let pp_ut ppf ut = Fmt.pf ppf "%a" pp_ut_cnt ut.cnt

let ut_equal t t' = t.hash = t'.hash

let ut_compare t t' = Stdlib.compare t.hash t'.hash

module OrdUt = struct
  type t = ut
  let compare t t' = ut_compare t t'

  let print ppf ut = pp_ut ppf ut
end

module Uuf = Uf(OrdUt)


(*------------------------------------------------------------------*)
(** {2 Formulas used in the constraint solving algorithm} *)
module Form = struct
  type ord = [`Eq | `Neq | `Leq]

  (** Literals *)
  type lit = ord * ut * ut

  (** Subset of formulas we use. *)
  type form =
    | Lit  of lit
    | Disj of form list        (* of length > 1 *)
    | Conj of form list        (* of length > 1 *)

  (** Conjunction of formulas *)
  type conjunction = form list

  (** Disjunction of formulas *)
  type disjunction = form list

  (*------------------------------------------------------------------*)
  (** Pretty printers *)

  let pp_lit fmt (od, ut1, ut2 : lit) =
    Fmt.pf fmt "@[<hv 2>(%a %a %a)@]"
      pp_ut ut1 Term.Lit.pp_ord (od :> Term.Lit.ord) pp_ut ut2

  let rec pp_form fmt = function
    | Lit l -> pp_lit fmt l
    | Disj l -> pp_disj fmt l
    | Conj l -> pp_conj fmt l

  and pp_disj fmt l =
    Fmt.pf fmt "@[<hv 2>%a@]"
      (Fmt.list
         ~sep:(fun fmt () -> Fmt.pf fmt " ||@ ")
         pp_form) l

  and pp_conj fmt l =
    Fmt.pf fmt "@[<hv 2>%a@]"
      (Fmt.list
         ~sep:(fun fmt () -> Fmt.pf fmt " &&@ ")
         pp_form) l

  (*------------------------------------------------------------------*)
  (** Smart constructors *)

  let disj = function
    | [] -> assert false
    | [f] -> f
    | l -> Disj l

  let conj = function
    | [] -> assert false
    | [f] -> f
    | l -> Conj l

  (*------------------------------------------------------------------*)
  (** Replace an atom by an equivalent list of atoms using only [`Eq], [`Neq]
      and [`Leq] *)
  let norm_atom (o, l, r) =
    match o with
    | `Eq  -> [(`Eq, l, r)]
    | `Neq -> [(`Neq, l, r)]
    | `Leq -> [(`Leq, l, r)]
    | `Geq -> [(`Leq, r, l)]
    | `Lt  -> (`Leq, l, r) :: [(`Neq, l, r)]
    | `Gt  -> (`Leq, r, l) :: [(`Neq, r, l)]


  let not_ord o = match o with
    | `Eq  -> `Neq
    | `Neq -> `Eq
    | `Leq -> `Gt
    | `Geq -> `Lt
    | `Lt  -> `Geq
    | `Gt  -> `Leq

  (*------------------------------------------------------------------*)
  (** Builds a conjunction of clauses form a trace literal *)
  let mk (memo : memo) (lit : Term.Lit.literal) : conjunction =
    let _mk atom =
      List.map (fun (od,t1,t2) ->
          Lit (od, term_to_ut memo t1, term_to_ut memo t2)
        ) (norm_atom atom)
    in

    (* Get a normalized trace literal. *)
    let rec doit (lit : Term.Lit.literal) : form list =     
      match lit with
      | `Neg, Happens t -> [Lit (`Eq,  term_to_ut memo t, uundef)]
      | `Pos, Happens t -> [Lit (`Neq, term_to_ut memo t, uundef)]

      | `Pos, (Comp ((_, _, _) as atom)) -> _mk atom

      (* We rewrite the negative literal as a positive literal, and recurse. *)
      | `Neg, (Comp (`Eq, t1, t2)) ->
        let lit = `Pos, Term.Lit.Comp (`Neq, t1, t2) in
        doit lit

      | `Neg, (Comp (`Neq, t1, t2)) ->
        let lit = `Pos, Term.Lit.Comp (`Eq, t1, t2) in
        doit lit

      (* Here, we need to build a disjunction to account for potentially
         undefined elements.
         Indeed, when ⋄ ∈ {≤, <, ≥, >}, we have:
         ¬ (x ⋄ y) ⇔ (undef(x) ∨ undef(y) ∨ (x □ y))
         where □ is the standard negation of ⋄ (e.g. if ⋄ = ≤, then □ = >) *)
      | `Neg, Comp ((`Leq|`Lt|`Geq|`Gt) as ord, u, v)
        when Term.ty u = Type.Timestamp ->
        let nord = not_ord ord in
        let form =
          disj (
            Lit (`Eq, term_to_ut memo u, uundef) ::
            Lit (`Eq, term_to_ut memo v, uundef) ::
            [conj (doit (`Pos, Comp (nord, u, v)))]) in

        [form]

      (* Type.Index *)
      | `Neg, Comp ((`Leq|`Lt|`Geq|`Gt), _, _) -> raise Unsupported

      (* If we have an arbitrary atom, try to open-it up as a disjunction or 
         conjunction etc.  *)
      | `Pos, Atom f ->
        if Term.is_and f then
          let forms = Term.decompose_ands f in
          [conj (List.map doit_form forms)]
        else if Term.is_or f then
          let forms = Term.decompose_ors f in
          [disj (List.map doit_form forms)]
        else if Term.is_impl f then
          let f1, f2 = oget (Term.destr_impl f) in
          [disj [doit_form (Term.mk_not f1); doit_form f2]]
        else if Term.is_not f then
          doit (`Neg, Atom (oget (Term.destr_not f)))
        else
          doit (`Pos, Comp (`Eq,  f, Term.mk_true))

      (* Idem as in [`Pos, Atom f], negating everything. *)
      | `Neg, Atom f ->
        if Term.is_and f then
          let forms = Term.decompose_ands f in
          [disj (List.map (fun f -> doit_form (Term.mk_not f)) forms)]
        else if Term.is_or f then
          let forms = Term.decompose_ors f in
          [conj (List.map (fun f -> doit_form (Term.mk_not f)) forms)]
        else if Term.is_impl f then
          let f1, f2 = oget (Term.destr_impl f) in
          [conj [doit_form f1; doit_form (Term.mk_not f2)]]
        else if Term.is_not f then
          doit (`Pos, Atom (oget (Term.destr_not f)))
        else 
          doit (`Neg, Comp (`Eq,  f, Term.mk_true))

    and doit_form (f : Term.term) : form =
      conj
        (match Term.Lit.form_to_literals f with
         | `Equiv l | `Entails l -> List.concat (List.map doit l)
        ) 
    in
    doit lit

  let mk_list memo (l : Term.terms) : conjunction =
    let l =
      List.concat_map (fun t ->
        match Term.Lit.form_to_literals t with
          | `Equiv l | `Entails l -> l
        ) l
    in
    List.concat_map (fun t ->       
        try mk memo t with
        | Unsupported ->
          dbg "@[<v 2>Dropping unsupported literal:@, @[%a@]@]"
            Term.Lit.pp t;
          []
      ) l
end


(*------------------------------------------------------------------*)
type constr_instance = {
  eqs     : (ut * ut) list;
  neqs    : (ut * ut) list;
  leqs    : (ut * ut) list;
  clauses : Form.disjunction list;   (* clauses that have not yet been split *)
  uf      : Uuf.t;
  memo    : memo;
}

(*------------------------------------------------------------------*)
let pp_constr_instance ~full fmt inst =
  let pp_el s fmt (ut1, ut2) =
    Fmt.pf fmt "%a %s %a" pp_ut ut1 s pp_ut ut2 in

  let pp_uf fmt =
    if full then
      Fmt.pf fmt "@[<hov 2>uf:@ %a@]@;" Uuf.print inst.uf
    else () in

  Fmt.pf fmt "@[<v 0>\
              %t\
              @[<hov 2>eqs:@ %a@]@;\
              @[<hov 2>leqs:@ %a@]@;\
              @[<hov 2>neqs:@ %a@]@;\
              @[<hov 2>clauses:@ %a@]\
              @]"
    pp_uf
    (Fmt.list ~sep:Fmt.comma (pp_el "=")) inst.eqs
    (Fmt.list ~sep:Fmt.comma (pp_el "≤")) inst.leqs
    (Fmt.list ~sep:Fmt.comma (pp_el "≠")) inst.neqs
    (Fmt.list ~sep:Fmt.comma Form.pp_disj) inst.clauses

(*------------------------------------------------------------------*)
let term_lit acc (_,ut1,ut2) = ut1 :: ut2 :: acc

let rec terms_form acc = function
  | Form.Lit lit -> term_lit acc lit
  | Form.Disj l
  | Form.Conj l -> terms_forms acc l

and terms_forms acc l = List.fold_left terms_form acc l

let all_terms (inst : constr_instance) =
  (* init, undef *)
  let terms = [uundef; uinit] in

  (* eqs, neqs, leqs *)
  let terms = List.fold_left (fun acc (a,b) ->
      a :: b :: acc
    ) terms (inst.eqs @ inst.leqs @ inst.neqs) in

  (* formulas *)
  List.fold_left terms_forms terms inst.clauses

let rec subterms acc x = match x.cnt with
  | UName (_,is) -> x :: is @ acc
  | UPred y      -> subterms (x :: acc) y
  | UVar _
  | UInit
  | UUndef -> x :: acc

(*------------------------------------------------------------------*)
let extends inst uts =
  let uts = List.fold_left subterms [] uts
            |> List.sort_uniq ut_compare in
  let uf = List.fold_left Uuf.extend inst.uf uts in
  { inst with uf = uf }

let add_elem el l = if List.mem el l then l else el :: l

let add_eqs ?(extend=true) inst (ut1,ut2) =
  let inst = if extend then extends inst [ut1;ut2] else inst in
  { inst with eqs  = add_elem (ut1,ut2) inst.eqs  }

let add_neqs ?(extend=true) inst (ut1,ut2) =
  let inst = if extend then extends inst [ut1;ut2] else inst in
  { inst with neqs  = add_elem (ut1,ut2) inst.neqs  }

let add_leqs ?(extend=true) inst (ut1,ut2) =
  let inst = if extend then extends inst [ut1;ut2] else inst in
  { inst with leqs  = add_elem (ut1,ut2) inst.leqs  }

let add_clause ?(extend=true) inst c =
  let uts = terms_forms [] c in
  let inst = if extend then extends inst uts else inst in
  { inst with clauses = c :: inst.clauses }

(** Add a formula to a constraint solving instance *)
let rec add_form ?(extend=true) (inst : constr_instance) (form : Form.form) =

  match form with
  | Form.Lit (`Eq,  ut1, ut2) -> add_eqs  ~extend inst (ut1,ut2)
  | Form.Lit (`Neq, ut1, ut2) -> add_neqs ~extend inst (ut1,ut2)
  | Form.Lit (`Leq, ut1, ut2) -> add_leqs ~extend inst (ut1,ut2)

  | Form.Disj l -> add_clause ~extend inst l

  | Form.Conj l -> List.fold_left (add_form ~extend) inst l

(** Add formulas to a constraint solving instance *)
let add_forms inst forms =
  List.fold_left add_form inst forms

(*------------------------------------------------------------------*)
(** Make the initial constraint solving instance. *)
let mk_instance memo (l : Form.form list) : constr_instance =
  let inst =
    { uf      = Uuf.create [];       (* dummy, real uf build after *)
      eqs     = [];
      leqs    = [];
      neqs    = [];
      clauses = [];
      memo; }
  in
  let l = Form.Lit (`Neq, uinit, uundef) :: l in
  let inst = List.fold_left (add_form ~extend:false) inst l in

  let elems = List.fold_left subterms [] (all_terms inst)
              |> List.sort_uniq ut_compare in

  let uf = Uuf.create elems in
  { inst with uf = uf; }

(*------------------------------------------------------------------*)
(** {2 Mgu application} *)

(** [mgu ut uf] applies the mgu represented by [uf] to [ut].
    Return [undef] if it contains a cycle.
    If [ext_support] is [true], add [ut] to [uf]'s support if necessary.
    Note that [mgu] normalizes [pred(init)] and [pred(undef)] into [undef]. *)
let mgu (uf : Uuf.t) (ut : ut) =
  let rec mgu_ uf ut lv =
    let uf, nut = mgu_aux uf ut lv in
    let uf = Uuf.extend uf nut in
    (Uuf.union uf ut nut, nut)

  (* Invariant: returns the representent of [ut] in [uf] *)
  and mgu_aux uf ut lv =
    let uf = Uuf.extend uf ut in

    if List.mem ut lv then (uf, uundef)
    else match ut.cnt with
      | UVar _ | UUndef | UInit ->
        let rut = Uuf.find uf ut in

        if ut_equal rut ut then (uf, rut)
        else mgu_ uf rut (ut :: lv)

      | UName (a,is) ->
        let rut = Uuf.find uf ut in
        if ut_equal rut ut then

          (* In that case, we need to apply the mgu on the index variable of
             the name. Since these cannot appear in [lv], we use the empty
             list [] *)
          let uf, nis_rev = List.fold_left (fun (uf,acc) x ->
              let uf, ni = mgu_ uf x [] in
              (uf, ni :: acc))
              (uf,[]) is in

          (uf, uname a (List.rev nis_rev))

        else mgu_ uf rut (ut :: lv)

      | UPred ut' ->
        let uf, nut' = mgu_ uf ut' lv in

        (* the [upred] smart constructor normalizes pred(undef) into undef) *)
        let pnut' = upred nut' in

        (* here, we are not certain that [pnut] is its own representent, so
           we ensure it. *)
        let uf = Uuf.extend uf pnut' in (* even if not ext_support *)
        let rpnut' = Uuf.find uf pnut' in
        if ut_equal rpnut' pnut' then (uf, rpnut')
        else mgu_ uf rpnut' (ut :: lv)
  in

  mgu_ uf ut []


let mgus uf uts =
  let uf, nuts_rev =
    List.fold_left
      (fun (uf,acc) ut ->
         let uf,nut = mgu uf ut in uf, nut :: acc)
      (uf,[]) uts
  in
  (uf, List.rev nuts_rev)


(*------------------------------------------------------------------*)
(** {2 Misc} *)

(*------------------------------------------------------------------*)
(** [get_class uf u] returns [u]'s equivalence class. *)
let get_class uf u =
  let uf, u = mgu uf u in

  let classes = Uuf.classes uf in (* remark: [Uuf.classes] uses memoisation *)

  List.find (fun classe ->
      List.exists (ut_equal u) classe
    ) classes


(* memoisation *)
let get_class =
  let module Memo = Uuf.Memo2 (Ut) in
  let memo = Memo.create 256 in
  fun uf (ut : ut) ->
    try Memo.find memo (uf,ut) with
    | Not_found ->
      let res = get_class uf ut in
      Memo.add memo (uf, ut) res;
      res

(*------------------------------------------------------------------*)
(** Returns true if the element cannot be equal to [init] *)
let is_not_init uf neqs (u : ut) =
  let uf, u = mgu uf u in

  (* Looks for an action [A(_)] in the equivalent class of [u].
     Note that, because [Pred _] is larger than [Name _] in [norm_ut_compare],
     we need to go through [u]'s full class. *)
  let u_class = get_class uf u in
  List.exists (fun u' -> match u'.cnt with
      | UName _ -> true
      | _ -> false
    ) u_class
  ||

  List.exists (fun (ut1,ut2) ->
      let uf,ut1 = mgu uf ut1 in
      let _, ut2 = mgu uf ut2 in
      (ut_equal ut2 uinit && ut_equal ut1 u) ||
      (ut_equal ut1 uinit && ut_equal ut2 u)
    ) neqs

(*------------------------------------------------------------------*)
(** [decomp u] returns the pair [(k,x]) where [k] is the maximal integer
    such that [u] equals [P^k(x)]. *)
let decomp u =
  let rec fdec i u = match u.cnt with
    | UPred u' -> fdec (i + 1) u'
    | _ -> (i,u) in
  fdec 0 u

(** [is_kpred uf ut] returns [true] if [u] is a k-predecessor of [v] in [uf]
    (for k > 0), i.e. [u = P^(v)]. *)
let is_kpred uf u v =
  let uf,u = mgu uf u in
  let _, v = mgu uf v in
  match decomp u, decomp v with
  | (k,y), (k',y') ->
    ut_equal y y' && k > k'

(** [is_undef uf ut] returns [true] if [ut] must be undefined in [uf]. *)
let is_undef uf ut = snd (mgu uf ut) = uundef
(* Remark: [uf] under-approximate equalities, hence any equality it contains
   is sound. *)

(** [is_undef uf ut] returns [true] if [ut] must be defined in [uf],
    under dis-equalities [neqs].
    This does not look for instances of the axiom:
    ∀τ, (happens(τ) ∧ τ ≠ init) ⇒ happens(pred(τ))
*)
let is_def ?explain:(explain=false) uf neqs ut =
  let uf, ut = mgu uf ut in

  let is_init = ut_equal ut uinit in
  if explain && is_init then
    dbg "is_def(%a): is equal to %a" pp_ut ut pp_ut uinit;

  let init_is_kpred = is_kpred uf uinit ut in
  if explain && init_is_kpred then
    dbg "is_def(%a): %a is its k-predecessor" pp_ut ut pp_ut uinit;

  (* Remark: we cannot use [uf] alone, as it is an under-approximation.
     Instead, we look for a contradiction in the conjunction of [uf] and
     known inequalities [neqs]. *)
  let swap u v = if ut_equal u uundef then v, u else u, v in
  let in_neqs = List.exists (fun (u,v) ->
      let uf,u = mgu uf u
      and _, v = mgu uf v in
      let u, v = swap u v in
      let b = (ut_equal v uundef) && (ut_equal ut u || is_kpred uf u ut) in
      (* ∃ k ≥ 0, u = P^k(ut) ∧ u ≠ undef  *)

      if explain && b then
        dbg "is_def(%a): is equal to %a, and %a ≠ %a"
          pp_ut ut pp_ut u pp_ut u pp_ut uundef;
      b
    ) neqs

  in is_init || init_is_kpred || in_neqs


(*------------------------------------------------------------------*)
(** {2 Equality handling} *)
(** This is alsmost Huet's unification *)


exception No_unif

 (** Pre-ordering [var > name > pred > init > undef].
     When choosing a representent in the union-find, we take the smallest.
     E.g. the representent of the set [(var x, undef)] is [undef] *)
let norm_ut_compare x y = match x.cnt, y.cnt with
  | UVar _, _      -> true
  | _, UVar _      -> false
  | UName _, _     -> true
  | _, UName _     -> false
  | UPred _, _     -> true
  | _, UPred _     -> false
  | UInit, _       -> true
  | _, UInit       -> false
  | UUndef, UUndef -> true

(** [let sx,sy = swap x y] guarantees that [x] is greater than [y] for the
   ordering [norm_ut_compare]. We use this to choose the representents in
   the union-find. *)
let swap x y = if norm_ut_compare x y then x, y else y, x

let no_mgu (x,defx) (y,defy) = match x.cnt, y.cnt with
  | UName (a,_), UName (a',_) ->
    if a <> a' && (defx || defy) then raise No_unif else ()
  | UInit, (UUndef | UName _)
  | (UName _ | UUndef), UInit -> raise No_unif
  (* Note that [UName _] can be equal to [UUndef] *)
  | _ -> ()

let unif inst eqs =
  let rec unif uf eqs = match eqs with
    | [] -> uf
    | (x,y) :: eqs ->
      let rx,ry = Uuf.find uf x, Uuf.find uf y in
      if ut_equal rx ry then unif uf eqs
      else
        let defrx = is_def uf inst.neqs rx
        and defry = is_def uf inst.neqs ry in

        let () = no_mgu (rx,defrx) (ry,defry) in
        let rx,ry = swap rx ry in

        (* Union always uses [ry]'s representant, in that case [ry] itself, as
           representant of the union of [rx] and [ry]'s classes. *)
        let uf = Uuf.union uf rx ry in

        let eqs = match rx.cnt, ry.cnt with
          | UName (_,isx), UName (_,isy) ->
            if defrx || defry
            then List.combine isx isy @ eqs
            else eqs

          | UPred a, UPred b -> (a,b) :: eqs
          | _ -> eqs in

        unif uf eqs
  in
  { inst with uf = unif inst.uf eqs }

(*------------------------------------------------------------------*)
(** Names unification *)

(* Now, it remains to unify name or init equalities that may have been missed. *)
let unif_idx inst =
  let aux_names idx_eqs (ut1,a1,is1) (ut2,a2,is2) =
    let def1 = is_def inst.uf inst.neqs ut1
    and def2 = is_def inst.uf inst.neqs ut2 in
    if not (def1 || def2) then idx_eqs
    else if a1 <> a2 then raise No_unif
    else List.combine is1 is2 @ idx_eqs in

  let rec aux idx_eqs (cl : ut list) = match cl with
    | [] -> idx_eqs
    | { cnt = UInit } :: cl' ->
      List.iter (fun ut -> match ut.cnt with
          | UName _ -> raise No_unif
          | _ -> ()
        ) cl';

      aux idx_eqs cl'

    | ({ cnt = UName (a1,is1) } as ut1) :: cl' ->
      let idx_eqs = List.fold_left (fun idx_eqs ut -> match ut.cnt with
          | UName (a2,is2) -> aux_names idx_eqs (ut1,a1,is1) (ut,a2,is2)
          | UInit -> raise No_unif
          | _ -> idx_eqs
        ) idx_eqs cl' in

      aux idx_eqs cl'

    | _ :: cl' -> aux idx_eqs cl' in

  let idx_eqs = List.fold_left aux [] (Uuf.classes inst.uf) in

  (* Unifies the indices equalities in eqs *)
  let finished = ref true in
  let rec unif_idx uf eqs = match eqs with
    | [] -> uf
    | (x,y) :: eqs ->
      let rx,ry = Uuf.find uf x, Uuf.find uf y in
      if ut_equal rx ry then unif_idx uf eqs
      else begin
        finished := false;
        unif_idx (Uuf.union uf rx ry) eqs end in

  let uf = unif_idx inst.uf idx_eqs in

  (!finished, { inst with uf = uf } )


(* Merges union-find classes with the same mgus. *)
let merge_eq_class uf =
  let reps =
    List.map (fun l -> match l with
        | [] -> raise (Failure "merge_eq_class")
        | x :: _ -> Uuf.find uf x) (Uuf.classes uf) in

  let aux uf cls = match cls with
    | [] -> uf
    | rcl :: cls' -> List.fold_left (fun uf rcl' ->
        let uf, nrcl = mgu uf rcl in
        let uf, nrcl' = mgu uf rcl' in

        if nrcl.cnt = nrcl'.cnt then Uuf.union uf rcl rcl'
        else uf) uf cls' in

  aux uf reps


let fpt_unif_idx inst =
  let rec do_fpt inst =
    let uf = merge_eq_class inst.uf in
    let finished, inst = unif_idx { inst with uf = uf } in
    if finished then inst else do_fpt inst in
  do_fpt inst

(*------------------------------------------------------------------*)
(** {2 Final unification algorithm} *)

let elems uf = List.flatten (Uuf.classes uf)

(** Returns the mgu for [eqs], starting from the mgu [uf] *)
let unify inst eqs =
  let inst = unif inst eqs |> fpt_unif_idx in
  (* We compute all mgu's, to check for cycles. *)
  let uf,_ = mgus inst.uf (elems inst.uf) in

  (* We check that [init] and [undef] are not equal. *)
  (* FIXME: this check is done in 3 different places *)
  let () =
    let _, rinit = mgu uf uinit in
    let _, rundef = mgu uf uundef in
    if rinit = rundef then raise No_unif
  in
  { inst with uf = uf; }

(*------------------------------------------------------------------*)
(** {2 Order models using graphs} *)

module UtG = Persistent.Digraph.Concrete(struct
    type t = ut
    let compare t t' = ut_compare t t'
    let equal t t' = t.hash = t'.hash
    let hash t = t.hash
  end)

module Scc = Components.Make(UtG)

(** Build the inequality graph. There is a edge from S to S' if there exits
    u in S and v in S' such that:
    i)   u <= v
    ii)  if u = P^{k+1}(t) and v = P^k(t) and u <> undef
    iii) or if u = init and v <> undef
    Remark: we use [mgu uf u] as a representant for the class of u *)
let build_graph (uf : Uuf.t) neqs leqs =
  let rec bg uf leqs g = match leqs with
    | [] -> uf, g
    | (u,v) :: leqs ->
      let uf, nu = mgu uf u in
      let uf, nv = mgu uf v in
      UtG.add_edge g nu nv
      |> bg uf leqs in          (* case i) *)

  let add_preds_and_init g =
    UtG.fold_vertex (fun v g ->
        let g = match v.cnt with
          | UPred u ->
            (* case ii) *)
            if is_def uf neqs u then UtG.add_edge g v u else g
          | _ -> g in

        (* case iii) *)
        if is_def uf neqs v then UtG.add_edge g uinit v else g
      ) g g in

  let uf, g = bg uf leqs UtG.empty in
  (uf, add_preds_and_init g)

(*------------------------------------------------------------------*)
let pp_scc fmt scc =
  Fmt.pf fmt "@[<hv 2>%a@]"
    (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt " =@ ") pp_ut) scc

let log_cycles sccs =
  let sccs = List.filter (fun scc -> List.length scc > 1) sccs in
  if List.length sccs > 0 then
    dbg "@[<v 2>Adding SCCs equalities:@, %a@]"
      (Fmt.list ~sep:(fun fmt () -> Fmt.pf fmt " &&@ ") pp_scc) sccs

(*------------------------------------------------------------------*)
(** For every SCC (x,x_1,...,x_n) in the graph, we add the equalities
    x=x_1 /\ ... /\ x = x_n   *)
let cycle_eqs g =
  let sccs = Scc.scc_list g in

  log_cycles sccs;

  List.fold_left (fun acc scc -> match scc with
      | [] -> raise (Failure "Constraints: Empty SCC")
      | x :: scc' -> List.fold_left (fun acc y -> (x,y) :: acc) acc scc')
    [] sccs

(*------------------------------------------------------------------*)
(** [leq_unify uf leqs neqs elems] compute the fixpoint of:
    - compute the inequality graph [g]
    - get [g] SCCs and the corresponding equalities
    - unify the new equalities *)
let rec leq_unify inst =
  let uf, g = build_graph inst.uf inst.neqs inst.leqs in
  let inst = { inst with uf = uf; } in
  let cycles = cycle_eqs g in
  let inst' = unify inst cycles in

  if Uuf.union_count inst.uf = Uuf.union_count inst'.uf then inst',g
  else leq_unify inst'


(*------------------------------------------------------------------*)
(** {2 Discrete Order Case Disjunction} *)

(** [min_pred uf g u x] returns [j] where [j] is the smallest integer such
    that [P^j(x) <= u] in the graph [g], if it exists.
    (hence [P^j] is the largest predecessor of [x] smaller than [u]).
    Precond: [g] must be a transitive graph, [u] normalized and [x] basic. *)
let min_pred uf g u x =
  let rec minp uf j cx =
    let uf, ncx = mgu uf cx in
    if UtG.mem_vertex g ncx then
      if UtG.mem_edge g ncx u || ut_equal ncx uinit then Some (uf,j)
      else minp uf (j+1) (upred ncx)
    else None
  in
  minp uf 0 x

(** [max_pred uf g u x] returns [j] where [j] is the largest integer such
    that [u <= P^j(x)] in the graph [g], if it exists, with a particular case
    if init occurs.
    (hence [P^j] is the smallest predecessor of [x] larger than [u]).
    Precond: [g] must be a transitive graph, [u] normalized and [x] basic. *)
let max_pred uf g u x =
  let rec maxp uf j cx =
    let uf, ncx = mgu uf cx in
    if ut_equal ncx uinit then
      if UtG.mem_edge g u ncx
      then Some (uf, j)
      else Some (uf, j - 1)
    else if (UtG.mem_vertex g ncx) && (UtG.mem_edge g u ncx) then
      maxp uf (j+1) (upred ncx)
    else
      Some (uf, j - 1)
  in
  let uf, nx = mgu uf x in
  if (UtG.mem_vertex g nx) && (UtG.mem_edge g u nx) then
    maxp uf 0 x
  else
    None

(** [nu] must be normalized and [base] basic *)
let no_case_disj uf (nu : ut) (base : ut) (minj : int) (maxj : int) =
  let nu_i, nu_y = decomp nu in
  ut_equal (snd (mgu uf base)) uinit  || (* ignore [init] as base-point *)
  ut_equal nu uinit ||                   (* idem for the point to split *)
  
  ut_equal (snd (mgu uf base)) uundef || (* ignore [⊥] as base-point *)
  ut_equal nu uundef ||                  (* idem for the point to split *)
  minj = maxj ||                      (* ignore segments of width 1 *)
  (nu_y = snd (mgu uf base)) && (maxj <= nu_i) && (nu_i <= minj)
  (* ignore segments if [nu] is already of the form [P^nu_i(x)] and
     [P^minj(x) ≤ P^nu_i(x) ≤ P^maxj(x)] *)

module UtGOp = Oper.P(UtG)

(** [kpred x i] return [P^i(x)] *)
let rec kpred x = function
  | 0 -> x
  | i -> kpred (upred x) (i - 1)

(** [g] must be transitive and [x] basic 
    Looks for [minj], [maxj] s.t. `u ∈ [P^minj(x); ...; P^maxj(x)]`. *)
let add_disj (uf : Uuf.t) (g : UtG.t) (u : ut) (base : ut) =
  let uf, nu = mgu uf u in
  obind (fun (uf,minj) ->
      obind (fun (uf,maxj) ->
          assert (minj >= maxj);        (* And not the converse ! *)
          if no_case_disj uf u base minj maxj then None
          else
            let uf, l = List.init (minj - maxj + 1) (fun i ->
                kpred base (maxj + i))
                        |> mgus uf in

            dbg "@[<v 2>Disjunction:@;\
                 to_split:%a@;\
                 minj:%d@;\
                 maxj:%d@;\
                 base:%a@]"
              pp_ut u
              minj maxj pp_ut base;
            Some (uf, List.map (fun x -> (nu,x)) l)
        ) (max_pred uf g nu base)
    ) (min_pred uf g nu base)


let for_all (f : UtG.vertex -> UtG.vertex -> bool) g : bool =
  let exception Found in
  try
    UtG.iter_edges (fun v v' ->
        if not (f v v') then raise Found
      ) g;
    true
  with Found -> false

(** Check that [instance] satisfies the dis-equality constraints and the rule:
    ∀ x, x <= P(x) <=> false
    Precondition: [g] must be transitive. *)
let neq_sat inst g : bool =
  let uf = inst.uf in
  (* All dis-equalities in neqs must hold *)
  List.for_all (fun (u,v) ->
      let violation = ut_equal (mgu uf u |> snd) (mgu uf v |> snd) in

      if violation then
        dbg "dis-equality %a ≠ %a violated" pp_ut u pp_ut v;

      not violation
    ) inst.neqs
  &&

  (* Looks for elements in undef equivalence class that are defined. *)
  (not (is_def ~explain:true uf inst.neqs uundef)) &&

  (* Look for contradiction in [g], i.e. an edge [u ≤ v] such that one of
     the following holds:
     - 1) [u = P^k(u)] and [v = P^k'(u)] for [k < k'].
     - 2) *)
  for_all (fun u v ->
      (* FIXME: we are recomputing mgu multiple times below *)
      let uf, u = mgu uf u in
      let uf, v = mgu uf v in

      let violation1 = is_kpred uf v u in

      if violation1 then
        dbg "contradiction: @[<hov>%a ≤ %a@] and@ \
             @[<hov>is_kpred %a %a@]"
          pp_ut u pp_ut v
          pp_ut v pp_ut u;

      let violation2 = is_undef uf u || is_undef uf v in

      if violation2 then begin
        let x = if is_undef uf u then u else v in
        dbg "contradiction: @[<hov>%a ≤ %a@] and@ \
             @[<hov>is_undef %a@]"
          pp_ut u pp_ut v pp_ut x
      end;

      not (violation1 || violation2)
    ) g


(*------------------------------------------------------------------*)

let get_basics uf elems =
  List.map (fun x -> mgu uf x |> snd) elems
  |> List.filter (fun x -> match x.cnt with UPred _ -> false | _ -> true)
  |> List.sort_uniq ut_compare

(*------------------------------------------------------------------*)
let log_segment_eq (eq : ut * ut) : unit =
  dbg "@[<v 2>Adding segment equality:@, %a@]"
    (Fmt.pair ~sep:(fun ppf () -> Fmt.pf ppf ", ")
       pp_ut pp_ut) eq

let log_split f =
  dbg "@[<v 2>Splitting clause:@, %a@]" Form.pp_disj f

let log_new_eqs eqs =
  let pp_eq fmt (ut1, ut2) =
    Fmt.pf fmt "%a = %a" pp_ut ut1 pp_ut ut2 in

  let pp_eqs fmt eqs =
    Fmt.pf fmt "@[<hv 2>%a@]"
      (Fmt.list ~sep:Fmt.comma pp_eq) eqs in

  dbg "@[<v 2>Adding new equalities:@, %a@]"
    pp_eqs eqs

let log_new_neqs neqs =
  let pp_neq fmt (ut1, ut2) =
    Fmt.pf fmt "%a ≠ %a" pp_ut ut1 pp_ut ut2 in

  let pp_neqs fmt eqs =
    Fmt.pf fmt "@[<hv 2>%a@]"
      (Fmt.list ~sep:Fmt.comma pp_neq) eqs in

  dbg "@[<v 2>Adding new dis-equalities:@, %a@]"
    pp_neqs neqs

let log_done () = dbg "@[<v 2>Model done@]"

let log_instr inst =
  dbg "@[<v 2>Solving:@ %a@]" (pp_constr_instance ~full:false) inst

(*------------------------------------------------------------------*)
(** Type of a model, which is a satisfiable and normalized instance, and the
    graph representing the inequalities of the instance (which is always
    transitive). *)
type model = {
  inst     : constr_instance;
  tr_graph : UtG.t;
}

let find_segment_disj instance g =
  let exception Found of Uuf.t * (ut * ut) list in

  let basics = get_basics instance.uf (elems instance.uf) in
  try
    let () = UtG.iter_vertex (fun (u : ut) ->
        List.iter (fun (x : ut) ->
            match add_disj instance.uf g u x with
            | None -> ()
            | Some (uf, l) -> raise (Found (uf,l))
          ) basics
      ) g in
    None
  with Found (x,y) -> Some (x, y)


(*------------------------------------------------------------------*)
(** Looks for instances of the rule:
    ∀ τ, (happens(τ) ∧ ¬happens(pred(τ))) ⇒ τ = init *)
let find_eq_init (inst : constr_instance) =
  let uf = inst.uf in

  List.filter_map (fun (ut1, ut2) ->
      let uf, uts = mgus uf [ut1;ut2] in
      let ut1, ut2 = Utils.as_seq2 uts in

      if ut_equal ut1 uundef || ut_equal ut2 uundef then None
      else
        let ut = if ut_equal ut1 uundef then ut2 else ut1 in
        let _, put = mgu uf (upred ut) in

        if ut_equal put uundef &&
           (not (ut_equal put uinit)) &&
           (not (ut_equal ut uinit))
        then Some (ut, uinit)
        else None
    ) inst.neqs

(*------------------------------------------------------------------*)
(** Looks for instances of the rule:
    ∀ τ τ', τ ≤ τ' ∧ pred(τ') = ⊥ ⇒ τ = τ' *)
let find_pred_undef (inst : constr_instance) graph =
  let uf = inst.uf in

  UtG.fold_edges (fun t t' new_eqs ->
      let uf, uts = mgus uf [t;t'] in
      let t, t' = Utils.as_seq2 uts in

      if is_undef uf (upred t') &&
         not (ut_equal t t')    (* do not add existing equalities *)
      then (t, t') :: new_eqs
      else new_eqs
    ) graph []

let find_new_eqs inst graph =
  let uf = inst.uf in
  let new_eqs = find_eq_init inst @ find_pred_undef inst graph in
  let new_eqs =
    (* we remove already known equalities *)
    List.filter (fun (t,t') ->
      let _uf, uts = mgus uf [t;t'] in
      let t, t' = Utils.as_seq2 uts in

        not (ut_equal t t')
      ) new_eqs
  in
  if new_eqs = [] then None else Some new_eqs

(*------------------------------------------------------------------*)
(** Check  *)
let undef_is_new inst ut =
  let uf, ut = mgu inst.uf ut in
  not (is_def uf inst.neqs ut)

let remove_dups inst uts =
  (* we remove duplicates *)
  let _, uts = List.fold_left (fun (uf,acc) x ->
      let uf, x = mgu uf x in uf, x :: acc
    ) (inst.uf,[]) uts in
  List.sort_uniq ut_compare uts


(** Looks for new undefined elements. *)
let find_new_undef inst g =
  let uf = inst.uf in
  let elems = elems uf in

  (* Looks for new instances of the rule:
     ∀τ, (happens(τ) ∧ τ ≠ init) ⇒ happens(pred(τ)) *)
  let undefs0 =
    List.filter_map (fun ut ->
        if is_not_init uf inst.neqs ut &&
           is_def uf inst.neqs ut &&
           undef_is_new inst (upred ut)
        then Some (upred ut)
        else None
      ) elems
  in

  (* Looks for new instances of the rule:
     ∀τ τ', τ ≤ τ' ⇒ happens(τ,τ') *)
  let undefs1 =
    UtG.fold_edges (fun ut1 ut2 undefs ->
        (if undef_is_new inst ut1 then [ut1] else []) @
        (if undef_is_new inst ut2 then [ut2] else []) @
        undefs
      ) g []
  in

  remove_dups inst (undefs0 @ undefs1)

(*------------------------------------------------------------------*)
(** [split instance] return a disjunction of satisfiable and normalized instances
    equivalent to [instance]. *)
let rec split (instance : constr_instance) : model list =
  try
    log_instr instance;

    let instance = unify instance instance.eqs in
    let instance,g = leq_unify instance in

    let g = UtGOp.transitive_closure g in

    begin match find_new_eqs instance g with
      | Some new_eqs ->
        log_new_eqs new_eqs;
        split { instance with eqs = new_eqs @ instance.eqs; }

      | None -> match find_new_undef instance g with
        | _ :: _ as undefs ->
          let new_neqs = List.map (fun ut -> ut, uundef) undefs in
          log_new_neqs new_neqs;
          split { instance with neqs = new_neqs @ instance.neqs; }


        | [] -> match neq_sat instance g with
          | false -> [] (* dis-equalities violated *)

          | true -> (* no violations for now *)
            (* Looking for segment disjunctions, e.g. if
               pred(τ) ≤ τ' ≤ τ
               then we know that (τ' = pred(τ) ∨ τ' = τ) *)
            match find_segment_disj instance g with
            | Some (uf, new_eqs) -> (* found a new segment disjunction *)
              List.map (fun eq ->
                  log_segment_eq eq;
                  split { instance with eqs = eq :: instance.eqs; uf}
                ) new_eqs
              |> List.flatten

            | None -> (* no new segment disjunction *)

              (* we look whether all initial clauses of the problem have
                 already been split *)
              match instance.clauses with
              | [] ->             (* no clause left, we are done *)
                log_done ();
                [ { inst = instance; tr_graph = g; } ]

              | disj :: clauses -> (* we found a clause to split *)
                log_split disj;

                let inst = { instance with clauses = clauses; } in
                let insts = List.map (fun f -> add_form inst f ) disj in
                List.map split insts
                |> List.flatten
    end
  with
  | No_unif ->
    dbg "@[<v 2>No_unif@]";
    []

let split_models instance =
  let models = split instance in

  dbg "@[<v 1>final models (%d models):@;%a@]"
    (List.length models)
    (Fmt.list (pp_constr_instance ~full:false))
    (List.map (fun x -> x.inst) models);

  models

(** The minimal models a of constraint.
    Here, minimanility means inclusion w.r.t. the predicates. *)
type models = memo * model list

(*------------------------------------------------------------------*)
let models_conjunct (terms : Term.terms) : models =
  let memo = mk_memo () in
  let l = Form.mk_list memo terms in
  let instance = mk_instance memo l in
  (memo, split_models instance)

(*------------------------------------------------------------------*)
(** Arrays of terms for memoisation *)
module TermArray : sig
  type t = Term.term
  val mk : t list -> t array
  module Memo : Ephemeron.S with type key = t array
end = struct
  type t = Term.term

  let mk l = Array.of_list (List.sort_uniq Stdlib.compare l)

  let equal t t' = Term.equal t t'

  (* FIXME: term hashconsing *)
  let hash = Term.hash

  module Memo = Ephemeron.Kn.Make(struct
      type _t = t
      type t = _t
      let equal = equal
      let hash = hash
    end)
end

(*------------------------------------------------------------------*)
(** Memoisation *)
let models_conjunct =
  let memo = TermArray.Memo.create 256 in
  fun (terms : Term.terms) ->
    let terms_array = TermArray.mk terms in
    try TermArray.Memo.find memo terms_array with
    | Not_found ->
      let res = models_conjunct terms in
      TermArray.Memo.add memo terms_array res;
      res

(** Exported.
    [models_conjunct] with time-out. *)
let models_conjunct
    (time_out : int)
    ?(exn = Tactics.Tactic_hard_failure (None, TacTimeout))
    (terms : Term.terms) : models
  = 
  Utils.timeout exn time_out models_conjunct terms

(*------------------------------------------------------------------*)
(** Exported. *)
let m_is_sat (models : models) = (snd models) <> []


(*------------------------------------------------------------------*)
(** [ext_support model ut] adds [ut] to the model union-find, if necessary, and
    return its normal form.
    There is no need to modify the rest of the model, since we are not adding
    an equality, disequality or inequality. *)
let ext_support (model : model) (ut : ut) =
  let uf, ut = mgu model.inst.uf ut in
  { model with inst = { model.inst with uf = uf } }, ut

let query_lit (model : model) (ord, ut1, ut2 : Form.lit) : bool =
  let model, u = ext_support model ut1 in
  let model, v = ext_support model ut2 in
  match ord with
  | `Eq -> ut_equal u v
  | `Leq -> UtG.mem_edge model.tr_graph u v
  | `Neq ->
    if ut_equal ut1 uundef || ut_equal ut2 uundef then
      (* when querying a happens, use the more precise [is_def] function *)
      let ut = if ut_equal ut1 uundef then ut2 else ut1 in
      is_def model.inst.uf model.inst.neqs ut

    else
      (* In that case, we are very unprecise, as we only check whether
         the inequality already appeared, modulo known equalities. *)
      List.exists (fun (a,b) ->
          let na, nb = mgu model.inst.uf a |> snd,
                       mgu model.inst.uf b |> snd in
          ((u = na) && (v = nb))
          || ((v = na) && (u = nb))
        ) model.inst.neqs

(* Note that we could not extend formulas easily to, e.g., negation, because
   we only under-approximate entailed equalities. *)
let rec query_form model (form : Form.form) = match form with
  | Form.Lit lit -> query_lit model lit
  | Form.Disj forms -> List.exists  (query_form model) forms
  | Form.Conj forms -> List.for_all (query_form model) forms

let query_one (memo : memo) (model : model) (at : Term.Lit.literal) : bool =
  try
    let cnf = Form.mk memo at in
    List.for_all (query_form model) cnf
  with Unsupported -> false

let query ~precise (models : models) (ats : Term.Lit.literals) =
  let memo, models = models in
  
  try
    assert (List.for_all (fun lit ->
        let ty = Term.Lit.ty lit in
        ty = Type.Index || ty = Type.Timestamp
      ) ats);

    (* if the conjunction of trace literals is  *)
    if
      List.for_all (fun model ->
          List.for_all (query_one memo model) ats
        ) models
    then true
    else if not precise then false
    else
      let forms =
        List.map (fun at -> Form.mk memo (Term.Lit.neg at)) ats
        |> List.flatten
      in
      let insts = List.map (fun model ->
          add_forms model.inst forms
        ) models in
      List.for_all (fun inst -> split_models inst = []) insts
  with Unsupported -> false

(* adds debugging information *)
let query ~precise (models : models) ats =
  dbg "%squery: %a"
    (if precise then "precise " else "") Term.Lit.pps ats;
  let b = query ~precise models ats in
  dbg "query result: %a : %a" Term.Lit.pps ats Fmt.bool b;
  b
    
(*------------------------------------------------------------------*)
(** [max_elems_model model elems] returns the maximal elements of [elems]
    in [model], *with* redundancy modulo [model]'s equality relation. *)
let max_elems_model (model : model) elems =
  let memo = mk_memo () in
  (* We normalize to obtain the representant of each timestamp. *)
  let model, l = List.fold_left (fun (model, l) ts ->
      let model, ut = ext_support model (term_to_ut memo ts) in
      (model, (ts,ut) :: l)
    ) (model,[]) elems in

  (* We keep elements that are maximal in [model] *)
  let melems = List.filter (fun (_,u) ->
      List.for_all (fun (_,u') ->
          ut_equal u u' || not (UtG.mem_edge model.tr_graph u u')
        ) l ) l
               |> List.map fst
               |> List.sort_uniq Stdlib.compare in

  model, melems

(** Exported *)
let maximal_elems ~precise (models : models) (elems : Term.term list) =
  let memo, models_list = models in
  
  (* Invariant: [maxs_acc] is sorted and without duplicates. *)
  let models_list, maxs =
    List.fold_left (fun (models_list, maxs_acc) m ->
        let m, m_maxs = max_elems_model m elems in
        (m :: models_list, List.merge_uniq Stdlib.compare maxs_acc m_maxs)
      ) ([],[]) models_list
  in
  let models_list = List.rev models_list in

  (* Now, we try to remove duplicates, i.e. elements which are in [maxs]
     and are equal in every model of [models], by picking an arbitrary
     element in each equivalence class. *)
  Utils.classes (fun ts ts' ->
      query ~precise (memo, models_list) [`Pos, Comp (`Eq,ts,ts')]
    ) maxs
  |> List.map List.hd

(** Exported *)
let get_ts_equalities ~precise (models : models) ts =
  Utils.classes (fun ts ts' ->
      query ~precise models [`Pos, Comp (`Eq,ts,ts')]
    ) ts

(** Exported *)
let get_ind_equalities ~precise (models : models) inds =
  Utils.classes (fun i j ->
      query ~precise models [`Pos, Comp (`Eq,Term.mk_var i,Term.mk_var j)]
    ) inds

(** Exported *)
let find_eq_action (models : models) (t : Term.term) =
  let memo, models_list = models in
  
  (* [action_model model t] returns an action equal to [t] in [model] *)
  let action_model model =
    let model, ut = ext_support model (term_to_ut memo t) in
    let uf = model.inst.uf in
    let classe = get_class uf ut in
    List.find_map (fun ut -> match ut.cnt with
        | UInit
        | UName _ -> Some (ut_to_term memo ut)
        | _ -> None
      ) classe
  in

  match t with
  | Term.Action _ -> Some t     (* already an action *)
  | _ ->
    (* compute an action equal to [t] in one model. *)
    match List.find_map action_model models_list with
    | None -> None
    | Some term ->
      (* check that [t] = [term] in all models. *)
      if query ~precise:true models [`Pos, Comp (`Eq,t,term)]
      then Some term
      else None


(*------------------------------------------------------------------*)
(** Context of an trace model *)
type trace_cntxt = {
  table  : Symbols.table;
  system : SE.fset;
  models : models option;
}

let make_context ~table ~system =
  { table ; system ; models = None }


(*------------------------------------------------------------------*)
(** Tests Suites *)

open Term
open Term.Lit
       
let env = ref Vars.empty_env
  
let mk_var ty v : Vars.var =
  let env', v = Vars.make `Approx !env ty v () in
  env := env';
  v

let mk_var_term ty v : Term.term = Term.mk_var (mk_var ty v)

let tau   = mk_var_term Type.ttimestamp "tau"
and tau'  = mk_var_term Type.ttimestamp "tau"
and tau'' = mk_var_term Type.ttimestamp "tau"
and tau3  = mk_var_term Type.ttimestamp "tau"
and tau4  = mk_var_term Type.ttimestamp "tau"
and i     = mk_var_term Type.tindex "i"
and i'    = mk_var_term Type.tindex "i"

let _, a = Symbols.Action.declare Symbols.builtins_table (L.mk_loc L._dummy "a") 1

let pb_eq1 = (Comp (`Eq,tau, mk_pred tau'))
             :: (Comp (`Eq,tau', mk_pred tau''))
             :: (Comp (`Eq,tau, mk_action a [i]))
             :: [Comp (`Eq,tau'', mk_action a [i'])]
and pb_eq2 = [Comp (`Eq,tau, mk_pred tau)]
and pb_eq3 = (Comp (`Eq,tau, mk_pred tau'))
             :: (Comp (`Eq,tau', mk_pred tau''))
             :: [Comp (`Eq,tau'', tau)]
and pb_eq4 = (Comp (`Eq,Term.init, mk_pred tau))
             :: (Comp (`Eq,tau, mk_pred tau'))
             :: (Comp (`Eq,tau', mk_pred tau''))
             :: (Comp (`Eq,tau, mk_action a [i]))
             :: [Comp (`Eq,tau'', mk_action a [i])]
and pb_eq5 = (Comp (`Eq,Term.init, mk_pred tau))
             :: (Comp (`Eq,tau, mk_pred tau'))
             :: (Comp (`Eq,tau', mk_action a [i']))
             :: (Comp (`Eq,tau, mk_action a [i]))
             :: (Comp (`Eq,tau'', mk_action a [i]))
             :: [Comp (`Eq,tau'', mk_action a [i'])]
and pb_eq6 = (Comp (`Eq,tau, mk_pred tau'))
             :: (Comp (`Eq,tau', mk_action a [i']))
             :: (Comp (`Eq,tau, mk_action a [i]))
             :: (Comp (`Eq,tau3, mk_action a [i]))
             :: [Comp (`Eq,tau'', mk_action a [i'])]
and pb_eq7 = (Comp (`Eq,tau, mk_pred tau'))
             :: (Comp (`Eq,tau', mk_pred tau''))
             :: (Comp (`Eq,tau, mk_action a [i]))
             :: [Comp (`Eq,tau'', mk_action a [i'])]
and pb_eq8 = (Comp (`Eq,tau, mk_pred tau'))
             :: (Comp (`Eq,tau', mk_pred tau''))
             :: [Comp (`Eq,tau'', tau3)]

let () =
  let exception Unsat in
  let exception Sat in
  let test = function
    | [] -> raise Unsat
    | _ -> raise Sat
  in
  
  let mk (l : Term.Lit.xatom list) =
    List.map (fun x -> lit_to_form (`Pos, x)) l
  in

  Checks.add_suite "Constr" [
    ("Cycles", `Quick,
     fun () ->
       let successes = [pb_eq1; pb_eq2; pb_eq3; pb_eq6; pb_eq7; pb_eq8]
       and failures = [pb_eq4; pb_eq5] in

       List.iteri (fun i pb ->
           Alcotest.check_raises ("sat" ^ string_of_int i) Sat
             (fun () -> test (snd @@ models_conjunct
                                TConfig.vint_timeout (mk pb))))
         successes;

       List.iteri (fun i pb ->
           Alcotest.check_raises ("unsat" ^ string_of_int i) Unsat
             (fun () -> test (snd @@ models_conjunct
                                TConfig.vint_timeout (mk pb))))
         failures;);

    ("Graph", `Quick,
     fun () ->
       let successes = [(Comp (`Leq, tau, tau'')) :: pb_eq1;

                        (Comp (`Neq, tau, tau3)) ::
                        (Comp (`Neq, tau3, tau'')) ::
                        (Comp (`Leq, tau, tau3)) ::
                        (Comp (`Leq, tau3, tau'')) ::
                        pb_eq1;

                       (Comp (`Neq, tau, tau3)) ::
                       (Comp (`Neq, tau4, tau'')) ::
                       (Comp (`Leq, tau, tau3)) ::
                       (Comp (`Leq, tau3, tau4)) ::
                       (Comp (`Leq, tau4, tau'')) ::
                       pb_eq1]
       and failures = [(Comp (`Leq, tau'', tau)) :: pb_eq1;

                       (Happens tau) ::
                       (Comp (`Neq, tau, tau3)) ::
                       (Comp (`Neq, tau3, tau4)) ::
                       (Comp (`Neq, tau4, tau'')) ::
                       (Comp (`Leq, tau, tau3)) ::
                       (Comp (`Leq, tau3, tau4)) ::
                       (Comp (`Leq, tau4, tau'')) ::
                       pb_eq1] in

       List.iteri (fun i pb ->
           Alcotest.check_raises ("graph(sat) " ^ string_of_int i) Sat
             (fun () -> test (snd @@ models_conjunct 
                                TConfig.vint_timeout (mk pb))))
         successes;

       List.iteri (fun i pb ->
           Alcotest.check_raises ("graph(unsat) " ^ string_of_int i) Unsat
             (fun () -> test (snd @@ models_conjunct
                               TConfig.vint_timeout (mk pb))))
         failures;);

    ("Complex queries", `Quick,
     fun () ->
       let open Term in
       let successes = [
         (* happens(t) && t = t' => t' <= t *)
         [mk_not (mk_impl (mk_ands [mk_happens tau; mk_eq tau tau']) (mk_leq tau' tau))];

         (* happens(t') && t = t' => t' <= t *)
         [mk_not (mk_impl (mk_ands [mk_happens tau'; mk_eq tau tau']) (mk_leq tau' tau))];

         (* (happens(t') || happens(t)) && t = t' => t' <= t *)
         [mk_not (mk_impl (mk_ands [mk_ors [mk_happens tau'; mk_happens tau]; mk_eq tau tau'])
                    (mk_leq tau' tau))];

         (* (happens(t) || happens(t')) && t = t' => t' <= t *)
         [mk_not (mk_impl (mk_ands [mk_ors [mk_happens tau; mk_happens tau']; mk_eq tau tau'])
                    (mk_leq tau' tau))];

         (* happens(t) && t = t' => t' >= t *)
         [mk_not (mk_impl (mk_ands [mk_happens tau; mk_eq tau tau']) (mk_geq tau' tau))];

         (* happens(t) && t = t' => (t' < t || t' > t || t' = t) *)
         [mk_not (mk_impl
                    (mk_ands [mk_happens tau; mk_eq tau tau'])
                    (mk_ors  [mk_lt tau' tau; mk_gt tau' tau; mk_eq tau' tau]))];

         (* happens(t) => happens(t') => (t' < t || t' > t || t' = t) *)
         [mk_not (mk_impl
                    (mk_ands [mk_happens tau; mk_happens tau'])
                    (mk_ors  [mk_lt tau' tau; mk_gt tau' tau; mk_eq tau' tau]))];
       ] in

       let failures = [
         (* t = t' => t' <= t *)
         [mk_not (mk_impl (mk_ands [mk_eq tau tau']) (mk_leq tau' tau))];

         (* t = t' => t' < t *)
         [mk_not (mk_impl (mk_ands [mk_eq tau tau']) (mk_lt tau' tau))];

         (* t = t' => t' >= t *)
         [mk_not (mk_impl (mk_ands [mk_eq tau tau']) (mk_geq tau' tau))];

         (* t = t' => t' > t *)
         [mk_not (mk_impl (mk_ands [mk_eq tau tau']) (mk_gt tau' tau))];

         (* happens(t) && t = t' => t' < t *)
         [mk_not (mk_impl (mk_ands [mk_happens tau; mk_eq tau tau']) (mk_lt tau' tau))];

         (* happens(t) && t = t' => t' < t *)
         [mk_not (mk_impl (mk_ands [mk_happens tau; mk_eq tau tau']) (mk_gt tau' tau))];

         (* happens(t) && t = t' => (t' < t || t' > t) *)
         [mk_not (mk_impl
                    (mk_ands [mk_happens tau; mk_eq tau tau'])
                    (mk_ors  [mk_lt tau' tau; mk_gt tau' tau]))];

         (* happens(t) => (t' < t || t' > t) *)
         [mk_not (mk_impl
                    (mk_ands [mk_happens tau])
                    (mk_ors  [mk_lt tau' tau; mk_gt tau' tau]))];

         (* happens(t) => (t' < t || t' = t) *)
         [mk_not (mk_impl
                    (mk_ands [mk_happens tau])
                    (mk_ors  [mk_lt tau' tau; mk_eq tau' tau]))];

         (* happens(t) => (t' > t || t' = t) *)
         [mk_not (mk_impl
                    (mk_ands [mk_happens tau])
                    (mk_ors  [mk_gt tau' tau; mk_eq tau' tau]))];
       ] in

       List.iteri (fun i pb ->       
           Alcotest.check_raises ("complex query " ^ string_of_int i) Unsat
             (fun () -> test (snd @@ models_conjunct TConfig.vint_timeout pb))
         ) successes;

       List.iteri (fun i pb ->       
           Alcotest.check_raises ("complex query " ^ string_of_int i) Sat
             (fun () -> test (snd @@ models_conjunct TConfig.vint_timeout pb))
         ) failures
    );
  ]
