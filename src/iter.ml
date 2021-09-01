open Utils

module Sv = Vars.Sv

(*------------------------------------------------------------------*)
(** Iterate over all boolean and message subterms.
  * Bound variables are represented as newly generated fresh variables.
  * When a macro is encountered, its expansion is visited as well. *)
class iter ~(cntxt:Constr.trace_cntxt) = object (self)
  method visit_message (t : Term.message) = match t with
    | Fun (_, _,l) -> List.iter self#visit_message l

    | Macro (ms,l,a) ->
      if l <> [] then failwith "Not implemented" ;
      begin
        match Macros.get_definition cntxt ms a with
        | `Undef | `MaybeDef -> assert false
        | `Def t -> self#visit_message t
      end

    | Name _ | Var _ -> ()

    | Diff(a, b) -> self#visit_message a; self#visit_message b

    | Seq (a, b) ->
      let _, s = Term.erefresh_vars `Global a in
      let b = Term.subst s b in
      self#visit_message b

    | Find (a, b, c, d) ->
      let _, subst = Term.refresh_vars `Global a in
      let b = Term.subst subst b in
      let c = Term.subst subst c in
      self#visit_message b; self#visit_message c; self#visit_message d

    | ForAll (vs,l) | Exists (vs,l) ->
      let _, subst = Term.erefresh_vars `Global vs in
      let l = Term.subst subst l in
      self#visit_message l

    | Atom (`Message (_, t, t')) ->
      self#visit_message t ;
      self#visit_message t'

    | Atom (`Index _) | Atom (`Timestamp _) | Atom (`Happens _) -> ()

end

(** Fold over all boolean and message subterms.
  * Bound variables are represented as newly generated fresh variables.
  * When a macro is encountered, its expansion is visited as well.
  * Note that [iter] could be obtained as a derived class of [fold],
  * but this would break the way we modify the iteration using inheritance.  *)
class ['a] fold ~(cntxt:Constr.trace_cntxt) = object (self)
  method fold_message (x : 'a) (t : Term.message) : 'a = match t with
    | Fun (_, _,l) -> List.fold_left self#fold_message x l

    | Macro (ms,l,a) ->
      if l<>[] then failwith "Not implemented" ;
      let t = match Macros.get_definition cntxt ms a with
        | `Undef | `MaybeDef -> assert false
        | `Def t -> t
      in
      self#fold_message x t

    | Name _ | Var _ -> x

    | Diff (a, b) -> self#fold_message (self#fold_message x a) b

    | Seq (a, b) ->
      let _, s = Term.erefresh_vars `Global a in
      let b = Term.subst s b in
      self#fold_message x b

    | Find (a, b, c, d) ->
      let _, s = Term.refresh_vars `Global a in
      let b = Term.subst s b in
      let c = Term.subst s c in
      let d = Term.subst s d in
      self#fold_message (self#fold_message (self#fold_message x b) c) d

    | ForAll (vs,l) | Exists (vs,l) ->
      let _, s = Term.erefresh_vars `Global vs in
      let l = Term.subst s l in
      self#fold_message x l

    | Atom (`Message (_, t, t')) ->
      self#fold_message (self#fold_message x t) t'

    | Atom (`Index _) | Atom (`Timestamp _) | Atom (`Happens _) -> x

end

(** Iterator that does not visit macro expansions but guarantees that,
  * for macro symbols [m] other that input, output, cond, exec, frame
  * and states, if [m(...)@..] occurs in the visited terms then
  * a specific expansion of [m] will have been visited, without
  * any guarantee on the indices and action used for that expansion,
  * because [get_dummy_definition] is used -- this behaviour is disabled
  * with [exact], in which case all macros will be expanded and must
  * thus be defined.
  * If [full] is false, may not visit all macros. *)
class iter_approx_macros ~exact ~(cntxt:Constr.trace_cntxt) = object (self)

  inherit iter ~cntxt as super

  val mutable checked_macros = []

  method visit_macro : Term.msymb -> Term.timestamp -> unit = fun ms a ->
    match Symbols.Macro.get_def ms.s_symb cntxt.table with
    | Symbols.(Input | Output | State _ | Cond | Exec | Frame) -> ()
    | Symbols.Global _ ->
      if exact then
        match Macros.get_definition cntxt ms a with
        | `Def def -> self#visit_message def
        | `Undef | `MaybeDef -> ()
        (* TODO: this may not always be the correct behavior. Check that
           all callees respect this convention *)

      else if not (List.mem ms.s_symb checked_macros) then begin
        checked_macros <- ms.s_symb :: checked_macros ;
        self#visit_message
          (Macros.get_dummy_definition cntxt.table cntxt.system ms)
      end

  method visit_message = function
    | Macro (ms,[],a) -> self#visit_macro ms a
    | m -> super#visit_message m

  method has_visited_macro mn = List.mem mn checked_macros

end

(** Collect occurrences of [f(_,k(_))] or [f(_,_,k(_))] for a function name [f]
    and name [k]. We use the exact version of [iter_approx_macros], otherwise we
    might obtain meaningless terms provided by [get_dummy_definition].
    Patterns must be of the form [f(_,_,g(k(_)))] if allow_funs is defined
    and [allows_funs g] returns true.
*)
class get_f_messages ?(drop_head=true)
    ?(fun_wrap_key=None)
    ~(cntxt:Constr.trace_cntxt) f k = object (self)
  inherit iter_approx_macros ~exact:true ~cntxt as super
  val mutable occurrences : (Vars.index list * Term.message) list = []
  method get_occurrences = occurrences
  method visit_message = function
    | Term.Fun ((f',_),_, [m;k']) as m_full when f' = f ->
      begin match k' with
        | Term.Name s' when s'.s_symb = k ->
          let ret_m = if drop_head then m else m_full in
          occurrences <- (s'.s_indices,ret_m) :: occurrences
        | _ -> ()
      end ;
      self#visit_message m ; self#visit_message k'

    | Term.Fun ((f',_), _,[m;r;k']) as m_full when f' = f ->
      begin match k', fun_wrap_key with
        | Term.Name s', None when s'.s_symb = k ->
          let ret_m = if drop_head then m else m_full in
          occurrences <- (s'.s_indices,ret_m) :: occurrences
        |Term.Fun ((f',_), _, [Term.Name s']), Some is_pk
          when is_pk f' && s'.s_symb = k ->
          let ret_m = if drop_head then m else m_full in
          occurrences <- (s'.s_indices,ret_m) :: occurrences
        | _ -> ()
      end ;
      self#visit_message m ; self#visit_message k'
    | Term.Var m -> assert false (* SSC must have been checked first *)
    | m -> super#visit_message m
end

(*------------------------------------------------------------------*)
(** {2 Occurrences} *)
type 'a occ = {
  occ_cnt  : 'a;
  occ_vars : Sv.t;             (* variables binded above the occurrence *)
  occ_cond : Term.message;     (* conditions above the occurrence *)
}

let pp_occ pp_cnt fmt occ =
  Fmt.pf fmt "[@[%a@] | ∃@[%a@], @[%a@]]"
    pp_cnt occ.occ_cnt
    (Fmt.list ~sep:Fmt.comma Vars.pp_e) (Sv.elements occ.occ_vars)
    Term.pp occ.occ_cond

type 'a occs = 'a occ list

(** Like [Term.tfold], but also propagate downward (globally refreshed)
    binded variables and conditions.
    If [Mode = `Delta _], try to expand macros.
    Over-approximation: we try to expand macros, even if they are at a timestamp
    that may not happen. *)
let tfold_occ : type b.
  mode:[`Delta of Constr.trace_cntxt | `NoDelta ] ->
  (fv:Sv.t -> cond:Term.message -> Term.eterm -> 'a -> 'a) ->
  fv:Sv.t -> cond:Term.message -> b Term.term -> 'a -> 'a =
  fun ~mode func ~fv ~cond t acc ->
  match t with
  | Term.ForAll (evs, t)
  | Term.Exists (evs, t) ->
    let evs, subst = Term.erefresh_vars `Global evs in
    let t = Term.subst subst t in
    let fv = Sv.union fv (Sv.of_list evs) in
    func ~fv ~cond (Term.ETerm t) acc

  | Term.Seq (is, t) ->
    let is, subst = Term.erefresh_vars `Global is in
    let t = Term.subst subst t in
    let fv = Sv.union fv (Sv.of_list is) in
    func ~fv ~cond (Term.ETerm t) acc

  | Term.Fun (fs, _, [c;t;e]) when fs = Term.f_ite ->
    func ~fv ~cond (Term.ETerm c) acc                               |>
    func ~fv ~cond:(Term.mk_and cond c) (Term.ETerm t)              |>
    func ~fv ~cond:(Term.mk_and cond (Term.mk_not c)) (Term.ETerm e)

  | Term.Find (is, c, t, e) ->
    let is, subst = Term.refresh_vars `Global is in
    let c, t = Term.subst subst c, Term.subst subst t in
    let fv1 = Sv.add_list fv is in

    func ~fv:fv1 ~cond (Term.ETerm c) acc                               |>
    func ~fv:fv1 ~cond:(Term.mk_and cond c) (Term.ETerm t)              |>
    func ~fv:fv1  ~cond:(Term.mk_and cond (Term.mk_not c)) (Term.ETerm e)

  | Term.Macro (m, l, ts) ->
    if l <> [] then failwith "Not implemented" ;

    let default () = func ~fv ~cond (Term.ETerm ts) acc in

    begin
      match mode with
      | `NoDelta -> default ()
      | `Delta constr ->
        match Macros.get_definition constr m ts with
        | `Def t -> func ~fv ~cond (Term.ETerm t) acc
        | `Undef | `MaybeDef -> default ()
    end

  | Term.Name   _
  | Term.Fun    _
  | Term.Pred   _
  | Term.Action _
  | Term.Var    _
  | Term.Diff   _
  | Term.Atom   _ ->
    Term.tfold (fun (Term.ETerm t) acc ->
        func ~fv ~cond (Term.ETerm t) acc
      ) t acc

(*------------------------------------------------------------------*)
(** {2 get_ftype} *)

type mess_occ = Term.message occ

type mess_occs = mess_occ list

type fsymb_matcher =
  | Type of Symbols.function_def
  | Symbol of Term.fsymb

let matching table (fn,vs) = function
  | Symbol fsymb -> fsymb = (fn,vs)
  | Type symtype -> Symbols.is_ftype fn symtype table


(** Looks for occurrences of subterms using a function symbol of the given kind
    (Hash, Dec, ...) or with the given head.
    Does not recurse below terms whose head is excluded by [excludesymtype]. *)
let get_f : type a.
  ?excludesymtype:Symbols.function_def ->
  ?allow_diff:bool ->
  Symbols.table ->
  fsymb_matcher ->
  a Term.term -> mess_occs =
  fun ?excludesymtype ?(allow_diff=false) table symtype t ->

  let rec get :
    type a. a Term.term -> fv:Sv.t -> cond:Term.message -> mess_occs =
    fun t ~fv ~cond ->
      let occs () =
        tfold_occ ~mode:`NoDelta (fun ~fv ~cond (Term.ETerm t) occs ->
            get t ~fv ~cond @ occs
          ) ~fv ~cond t []
      in

      match t with
      | Term.Fun ((fn,vs),_,l)  ->
        let head_occ =
          if matching table (fn,vs) symtype
          then [{ occ_cnt  = t;
                  occ_vars = fv;
                  occ_cond = cond; }]
          else []
        in

        let rec_occs = match excludesymtype with
          | Some ex when Symbols.is_ftype fn ex table -> []
          | _ -> occs ()
        in

        head_occ @ rec_occs

      | Term.Diff (Term.Fun _, Term. Fun _) when allow_diff ->
        let head_occ =
          if (match Term.pi_term PLeft t, Term.pi_term PRight t with
              | (Fun (fl,_,ll),Fun (fr,_,lr))
                when (matching table fl symtype
                      && matching table fr symtype ) -> true
              | _ -> false )
          then [{ occ_cnt  = t;
                  occ_vars = fv;
                  occ_cond = cond; }]
          else []
        in
        head_occ @ (occs ())

      | _ -> occs ()
  in

  get t ~fv:Sv.empty ~cond:Term.mk_true


let get_ftypes : type a.
  ?excludesymtype:Symbols.function_def ->
  Symbols.table ->
  Symbols.function_def ->
  a Term.term -> mess_occs = fun ?excludesymtype table symtype t ->
  get_f  ?excludesymtype table (Type symtype) t

let get_fsymb : type a.
  ?excludesymtype:Symbols.function_def ->
  ?allow_diff:bool ->
  Symbols.table ->
  Term.fsymb ->
  a Term.term -> mess_occs = fun ?excludesymtype ?allow_diff table symtype t ->
  get_f  ?excludesymtype ?allow_diff table (Symbol symtype) t

(*------------------------------------------------------------------*)
(** {2 Find [h(_, k)]} *)

(** pair of the key indices and the term *)
type hash_occ = (Vars.index list * Term.message) occ

type hash_occs = hash_occ list

(** Collect direct occurrences of [f(_,k(_))] or [f(_,_,k(_))] where [f] is a
    function name [f] and [k] a name [k].
    Over-approximation: we try to expand macros, even if they are at a timestamp
    that may not happen. *)
let get_f_messages_ext : type a.
  ?drop_head:bool ->
  ?fun_wrap_key:'b ->
  ?fv:Sv.t ->
  cntxt:Constr.trace_cntxt ->
  Term.fname ->
  Term.name ->
  a Term.term -> hash_occs
  =
  fun ?(drop_head=true) ?(fun_wrap_key=None) ?(fv=Sv.empty) ~cntxt f k t ->

  let rec get :
    type a. a Term.term -> fv:Sv.t -> cond:Term.message -> hash_occs =
    fun t ~fv ~cond ->
      let occs () =
        tfold_occ ~mode:(`Delta cntxt) (fun ~fv ~cond (Term.ETerm t) occs ->
            get t ~fv ~cond @ occs
          ) ~fv ~cond t []
      in

      match t with
      | Term.Fun ((f',_),_, [m;k']) as m_full when f' = f ->
        let occs =
          match k' with
          | Term.Name s' when s'.s_symb = k ->
            let ret_m = if drop_head then m else m_full in
            [{ occ_cnt  = s'.s_indices,ret_m;
               occ_vars = fv;
               occ_cond = cond; }]
          | _ -> []
        in
        occs @ get m ~fv ~cond @ get k' ~fv ~cond

      | Term.Fun ((f',_), _, [m;r;k']) as m_full when f' = f ->
        let occs =
          match k', fun_wrap_key with
          | Term.Name s', None when s'.s_symb = k ->
            let ret_m = if drop_head then m else m_full in
            [{ occ_cnt  = s'.s_indices,ret_m;
               occ_vars = fv;
               occ_cond = cond; }]

          |Term.Fun ((f',_), _, [Term.Name s']), Some is_pk
            when is_pk f' && s'.s_symb = k ->
            let ret_m = if drop_head then m else m_full in
            [{ occ_cnt  = s'.s_indices,ret_m;
               occ_vars = fv;
               occ_cond = cond; }]
          | _ -> []
        in
        occs @ get m ~fv ~cond @ get k' ~fv ~cond

      | Term.Var m when Type.equalk (Vars.kind m) Type.KMessage -> assert false
      (* SSC must have been checked first *)

      | _ -> occs ()
  in

  get t ~fv ~cond:Term.mk_true


(*------------------------------------------------------------------*)
(** {2 If-Then-Else} *)

type ite_occ = (Term.message * Term.message * Term.message) occ

type ite_occs = ite_occ list

(** Does not remove duplicates.
    Does not look below macros. *)
let get_ite_term : type a. Constr.trace_cntxt -> a Term.term -> ite_occs =
  fun constr t ->

  let rec get :
    type a. a Term.term -> fv:Sv.t -> cond:Term.message -> ite_occs =
    fun t ~fv ~cond ->
      let occs =
        tfold_occ ~mode:`NoDelta (fun ~fv ~cond (Term.ETerm t) occs ->
            get t ~fv ~cond @ occs
          ) ~fv ~cond t []
      in

      match t with
      | Fun (f,_,[c;t;e]) when f = Term.f_ite ->
        let occ = {
          occ_cnt  = c,t,e;
          occ_vars = fv;
          occ_cond = cond; }
        in
        occ :: occs

      | _ -> occs
  in

  get t ~fv:Sv.empty ~cond:Term.mk_true

(*------------------------------------------------------------------*)
(** occurrence of a macro [n(i,...,j)] *)
type macro_occ = Term.msymb occ

type macro_occs = macro_occ list

exception Var_found

let is_global ms table =
  match Symbols.Macro.get_def ms.Term.s_symb table with
  | Symbols.Global _ -> true
  | _ -> false

(** Looks for macro occurrences in a term.
    - [mode = `FullDelta]: all macros that can be expanded are ignored.
    - [mode = `Delta]: only Global macros are expanded (and ignored)
    Raise @Var_found if a term variable occurs in the term. *)
let get_macro_occs : type a.
  mode:[`FullDelta | `Delta ] ->
  Constr.trace_cntxt ->
  a Term.term ->
  macro_occs
  =
  fun ~mode constr t ->

  let rec get :
    type a. a Term.term -> fv:Sv.t -> cond:Term.message -> macro_occs =
    fun t ~fv ~cond ->
      match t with
      | Term.Var v when Type.equalk (Vars.kind v) Type.KMessage ->
        raise Var_found

      | Term.Macro (ms, l, ts) ->
        assert (l = []);
        let default () =
          [{ occ_cnt  = ms;
             occ_vars = fv;
             occ_cond = cond; }]
        in

        if mode = `FullDelta || is_global ms constr.table then
          match Macros.get_definition constr ms ts with
          | `Def t -> get t ~fv ~cond
          | `Undef | `MaybeDef -> default ()
        else default ()

      | _ ->
        tfold_occ ~mode:`NoDelta
          (fun ~fv ~cond (Term.ETerm t) occs ->
             get t ~fv ~cond @ occs
          ) ~fv ~cond t []
  in
  get t ~fv:Sv.empty ~cond:Term.mk_true

(*------------------------------------------------------------------*)
(** fold over macros defined at a given description.
    Also folds over global macros if [globals] is [true]. *)
let fold_descr
    ~(globals:bool)
    (f :
       Symbols.macro Symbols.t -> (* macro symbol [ms] *)
       Vars.index list ->         (* indices [is] of [ms] *)
       Symbols.macro_def ->       (* macro definition *)
       Term.message ->            (* term [t] defining [ms(is)] *)
       'a -> 'a)
    (table  : Symbols.table)
    (system : SystemExpr.t)
    (descr : Action.descr)
    (init : 'a) : 'a
  =
  let mval = f Symbols.out [] Symbols.Output (snd descr.output) init in
  let mval = f Symbols.cond [] Symbols.Cond (snd descr.condition) mval in

  (* fold over state macros *)
  let mval =
    List.fold_left (fun mval (st, t) ->
        let is = st.Term.s_indices in
        let mdef =
          Symbols.State (List.length is, st.Term.s_typ)
        in
        f st.Term.s_symb is mdef t mval
      ) mval descr.updates
  in

  if not globals then mval
  else
    let ts = SystemExpr.action_to_term table system descr.action in
    (* fold over global macros in scope of [descr.action] *)
    List.fold_left (fun mval (mg : Symbols.macro Symbols.t) ->
        let cntxt = Constr.{ system; table; models = None; } in
        let mdef, is_arr,ty = match Symbols.Macro.get_def mg table with
          | Global (is,ty) as mdef -> mdef, is, ty
          | _ -> assert false
        in
        let is = List.take is_arr descr.Action.indices in
        let msymb = Term.mk_isymb mg ty is in
        let t = match Macros.get_definition cntxt msymb ts with
          | `Def t -> t
          | _ -> assert false
        in
        f mg is mdef t mval
      ) mval descr.globals

(*------------------------------------------------------------------*)
module Ss = Symbols.Ss(Symbols.Macro)
module Ms = Symbols.Ms(Symbols.Macro)

let is_glob table ms =
  match Symbols.Macro.get_def ms table with
  | Symbols.Global _ -> true
  | _ -> false

(*------------------------------------------------------------------*)
module Mset : sig
  (** Set of macros over some indices.
        [{ msymb   = m;
           indices = vars; }]
      represents the set of terms [\{m@τ | ∀ vars, τ \}]. *)
  type t = private {
    msymb   : Term.msymb;
    indices : Vars.index list;
  }

  val mk :
    env:Sv.t ->
    msymb:Term.msymb ->
    indices:(Vars.index list) ->
    t 

  val pp   : Format.formatter -> t      -> unit
  val pp_l : Format.formatter -> t list -> unit

  (** Compute the lub of two msets (w.r.t set inclusion).
      Must be called on sets with the same macro symbol. *)
  val join : t -> t -> t

  (** [mset_incl tbl system s1 s2] check if all terms in [s1] are
      members of [s2]. *)
  val incl : Symbols.table -> SystemExpr.t -> t -> t -> bool

  (** simpl mset builder, when the macro symbol is not indexed. *)
  val mk_simple : Symbols.macro Symbols.t -> Type.tmessage -> t 
end = struct
  type t = {
    msymb   : Term.msymb;
    indices : Vars.index list;
  }

  let mk ~env ~msymb ~indices : t =
    let indices = Sv.diff (Sv.of_list1 indices) env in
    let indices =
      List.map (fun ev -> Vars.ecast ev Type.KIndex) (Sv.elements indices)
    in
    { msymb; indices }


  let pp fmt (mset : t) =
    let vars = List.map Vars.evar mset.indices in

    Fmt.pf fmt "@[<hv 2>{ @[%a@]@@_ |@ %a}@]"
      Term.pp_msymb mset.msymb
      (Fmt.list ~sep:Fmt.comma Vars.pp_e) vars

  let pp_l fmt (mset_l : t list) =
    Fmt.pf fmt "@[<v 0>%a@]"
      (Fmt.list ~sep:Fmt.sp pp) mset_l


  (** Compute the lub of two msets (w.r.t set inclusion).
      Must be called on sets with the same macro symbol. 

      A mset is a set of terms of the form:
         [\{m(i₁, ..., iₙ)@τ | ∀ vars, τ \}]
      where [m] is a macro symbol, [τ] is a timestamp variable, and
      [i₁,...,iₙ] are not necessarily distinct index variables that can appear
      in [vars], but don't have to.

      Alternatively, a mset is a set of terms of the form:

         [\{m(j₁, ..., jₖ)@τ | ∀ j₁, ..., jₖ s.t. 
                                j₁, ..., jₖ ⊢ E₁, ..., Eₙ ∧ ∀ τ \}]

      where [j₁, ..., jₖ] are *distinct* index variables, and [E₁, ..., Eₙ]
      are equalities between index variables (not necessarily all in
      [j₁, ..., jₖ]).
      Such a set is fully characterized by the symbol [m] (which fixes the  
      arity [k]), and by the equalities [E₁, ..., Eₙ].

      Hence, given two such sets [S] and [S'] characterized by
      ([m], [E₁, ..., Eₙ]) and ([m], [F₁, ..., Fₘ]) (note the same macro symbol), 
      the least upper bound (among msets, w.r.t. set inclusion) [Sₗ] of 
      [S ∪ S'] is the macro set characterized by [G₁, ..., Gₗ] where: 

      [\{G₁, ..., Gₗ\} = \{ G | E₁, ..., Eₙ ⊢ G ∧ F₁, ..., Fₘ ⊢ G\}]

      The algorithm below is based on that observation. Of course, we do not 
      test all equalities [G] (there are too many of them). Essentially, we 
      check a complete base of such equalities, which fully characterize [Sₗ].
  *)
  let join (a : t) (b : t) : t = 
    let a_ms, b_ms = a.msymb, b.msymb in
    assert (a_ms.s_symb = b_ms.s_symb);

    let l = List.length a_ms.s_indices in
    (* [arr] will be the vector of indices of the macro symbol we 
       are building *)
    let arr = Array.make l None in

    (* index variable universally quantified in the final set *)
    let indices_r = ref [] in

    (* we fill [arr], while keeping [indices_r] updated *)
    Array.iteri (fun i cnt ->
        match cnt with
        | Some _ -> ()        (* already filled, nothing to do *)
        | None ->
          let v_a = List.nth a_ms.s_indices i in
          let v_b = List.nth b_ms.s_indices i in

          let univ_var, v = 
            match List.mem v_a a.indices, List.mem v_b b.indices with
            | false, false ->   
              (* [v_a] and [v_b] are constant w.r.t., resp., [a] and [b]
                 In that case: 
                 - if [v_a] = [v_b] then we use [v_a] 
                 - otherwise, we must use a fresh universally quantified var. *)
              if v_a = v_b
              then false, v_a
              else true, Vars.make_new Type.Index "i" 

            (* [v_a] or [v_b] is not a constant.
               In that case, use a universally quantified variable. *)
            | true, _ -> true, Vars.make_new_from v_a 
            | _, true -> true, Vars.make_new_from v_b
          in

          (* update [indices_r] *)
          indices_r := if univ_var then v :: !indices_r else !indices_r;

          List.iteri2 (fun j u_a u_b -> 
              if u_a = v_a && u_b = v_b then begin
                assert (Array.get arr j = None);
                Array.set arr j (Some v)
              end
            ) a_ms.s_indices b_ms.s_indices
      ) arr;

    let join_is = Array.fold_right (fun a acc -> oget a :: acc) arr [] in
    let join_ms = Term.mk_isymb a_ms.s_symb a_ms.s_typ join_is in
    mk ~env:Sv.empty ~msymb:join_ms ~indices:(!indices_r)

  let incl table system (s1 : t) (s2 : t) : bool
    =
    let tv = Vars.make_new Type.Timestamp "t" in
    let term1 = Term.mk_macro s1.msymb [] (Term.mk_var tv) in
    let term2 = Term.mk_macro s2.msymb [] (Term.mk_var tv) in

    let pat2 =
      Match.{ pat_term = term2;
              pat_tyvars = [];
              pat_vars = Sv.of_list1 s2.indices;}
    in
    match Match.T.try_match table system term1 pat2 with
    | Match _ -> true
    | FreeTyv | NoMatch _ -> false

  let mk_simple (m : Symbols.macro Symbols.t) ty : t = 
    let msymb = Term.mk_isymb m ty [] in
    mk ~env:Sv.empty ~msymb ~indices:[]
end    

module MsetAbs : sig
  (** abstract value containing one mset per macro symbol. *)
  type t = (Term.mname * Mset.t) list

  val pp : Format.formatter -> t -> unit

  (** join a single [mset] into an full abstract value. *)
  val join_single : Mset.t -> t -> t

  (** join operator. *)
  val join : t -> t -> t

  (** [incl abs1 abs2] checks if [abs1 ⊆ abs2]. *)
  val incl : Symbols.table -> SystemExpr.t -> t -> t -> bool

  (** [diff abs1 abs2] over-approximates [abs1 \ abs2]. *)
  val diff : Symbols.table -> SystemExpr.t -> t -> t -> t
end = struct
  type t = (Term.mname * Mset.t) list

  let pp fmt (abs : t) : unit =
    let pp_one fmt (mname, mset) = 
      Fmt.pf fmt "@[<h>%a: %a@]" Symbols.pp mname Mset.pp mset
    in
    Fmt.pf fmt "@[<v 0>%a@]" (Fmt.list ~sep:Fmt.cut pp_one) abs

  let join_single (mset : Mset.t) (msets : t) : t =
    let name = mset.msymb.s_symb in 
    if List.mem_assoc name msets then
      List.assoc_up name (fun b -> Mset.join mset b) msets
    else (name, mset) :: msets

  let join (abs1 : t) (abs2 : t) : t =
    List.fold_left (fun abs (_, mset) -> join_single mset abs) abs1 abs2

  let incl 
      (table  : Symbols.table)
      (system : SystemExpr.t)
      (abs1   : t) 
      (abs2   : t) : bool
    =
    List.for_all (fun (mn, m1) ->
        try 
          let m2 = List.assoc mn abs2 in
          Mset.incl table system m1 m2
        with Not_found -> false
      ) abs1

  let diff
      (table  : Symbols.table)
      (system : SystemExpr.t)
      (abs1   : t) 
      (abs2   : t) : t
    =
    List.filter (fun (mn, m1) ->
        try 
          let m2 = List.assoc mn abs2 in
          not (Mset.incl table system m1 m2)
        with Not_found -> true
      ) abs1
end

(*------------------------------------------------------------------*)
(** Return an over-approximation of the the macros reachable from a term
    in any trace model. *)
let macro_support : type a.
  env:Sv.t ->
  Constr.trace_cntxt ->
  a Term.term ->
  MsetAbs.t
  =
  fun ~env cntxt term ->
  let get_msymbs : type a. 
    mode:[`Delta | `FullDelta ] -> a Term.term -> MsetAbs.t
    = fun ~mode term ->
      let occs = get_macro_occs ~mode cntxt term in
      let msets = List.map (fun occ -> 
          let indices = occ.occ_cnt.Term.s_indices in
          Mset.mk ~env ~msymb:occ.occ_cnt ~indices) occs 
      in
      List.fold_left (fun abs mset -> MsetAbs.join_single mset abs) [] msets 
  in

  let init = get_msymbs ~mode:`FullDelta term in
  
  let do1 (sm : MsetAbs.t) =
    (* special cases for Input, Frame and Exec, since they do not appear in the
       action descriptions. *)
    let sm = 
      if List.mem_assoc Symbols.inp sm 
      then MsetAbs.join_single (Mset.mk_simple Symbols.frame Type.Message) sm 
      else sm 
    in
    let sm =
      if List.mem_assoc Symbols.frame sm
      then 
        MsetAbs.join_single (Mset.mk_simple Symbols.exec Type.Boolean)
          (MsetAbs.join_single (Mset.mk_simple Symbols.out Type.Message) sm)
      else sm
    in
    let sm =
      if List.mem_assoc Symbols.exec sm
      then MsetAbs.join_single (Mset.mk_simple Symbols.cond Type.Boolean) sm
      else sm
    in

    SystemExpr.fold_descrs (fun descr sm ->
        fold_descr ~globals:true (fun msymb is _ t sm ->
            if List.mem_assoc msymb sm then
              (* we compute the substitution which we will use to instantiate 
                 [t] on the indices of the macro set in [sm]. *)
              let subst = 
                let mset = List.assoc msymb sm in
                List.map2 (fun i j -> 
                    Term.ESubst (Term.mk_var i, Term.mk_var j)
                  ) is mset.Mset.msymb.Term.s_indices                 
              in
              let t = Term.subst subst t in

              MsetAbs.join (get_msymbs ~mode:`Delta t) sm

            else sm
          ) cntxt.table cntxt.system descr sm
      ) cntxt.table cntxt.system sm
  in

  let abs_incl = MsetAbs.incl cntxt.table cntxt.system in

  (* reachable macros from [init] *)
  let s_reach = Utils.fpt abs_incl do1 init in
  
  (* we now try to minimize [s_reach], by removing as many global macros as
     possible *)

  let s_reach_no_globs =
    List.filter (fun (ms,_) -> not (is_glob cntxt.table ms)) s_reach
  in
  (* [s_reach'] are macros reachable from non-global macros in [s_reach] *)
  let s_reach' = Utils.fpt abs_incl do1 s_reach_no_globs in
  
  assert (abs_incl s_reach' s_reach);

  (* global macros reachable from s_reach' *)
  let s_reach'_glob =
    List.filter (fun (ms, _) -> is_glob cntxt.table ms) s_reach'
  in

  (* we remove from [s_reach] all global macros reachable from non-global
     macros in [s_reach] *)
  MsetAbs.diff cntxt.table cntxt.system s_reach s_reach'_glob


(** An indirect occurrence of a macro term, used as return type of 
    [fold_macro_support]. The record:

      [ { iocc_aname = n;
          iocc_vars = is; 
          iocc_cnt = t; 
          iocc_action = a;
          iocc_sources = srcs; } ]

    states that, for all indices [is], [t] is the body of a macro of action [a], 
    and that this macro may appear in the translation of any of the terms in [srcs]
    in some trace model.
    Notes: 
    - [env ∩ is = ∅]
    - if [env] are the free index variables of [srcs], then the free index
      variables of [t] and [a] are included in [env ∪ is].
*)
type iocc = { 
  iocc_aname   : Symbols.action Symbols.t;
  iocc_action  : Action.action;
  iocc_vars    : Vars.index list;
  iocc_cnt     : Term.message;
  iocc_sources : Term.message list; 
}

let pp_iocc fmt (o : iocc) : unit = 
  Fmt.pf fmt "@[<v 2>[%a(%a):@;cnt: @[%a@]@;sources: @[%a@]@;fv: @[%a@]]@]"
    Symbols.pp o.iocc_aname
    Vars.pp_list (Action.get_indices o.iocc_action)
    Term.pp o.iocc_cnt
    (Fmt.list ~sep:Fmt.comma Term.pp) o.iocc_sources
    (Fmt.list ~sep:Fmt.comma Vars.pp) o.iocc_vars

(** Folding over all macro descriptions reachable from some terms.
    [env] must contain the free variables of [terms].  *)
let _fold_macro_support 
    (func : ((unit -> Action.descr) -> iocc -> 'a -> 'a)) 
    (cntxt : Constr.trace_cntxt)
    (env : Vars.env)
    (terms : Term.message list) 
    (init : 'a) : 'a 
  =
  let env = Vars.to_set env in

  (* association list of terms and their macro support *)
  let sm : (Term.message * MsetAbs.t) list = 
    List.map (fun src -> (src, macro_support ~env cntxt src)) terms 
  in

  (* reversing the association map: we want to map macros to 
     pairs of possible sources and macro set *)
  let macro_occs : (Term.message list * Mset.t) Ms.t = 
    List.fold_left (fun macro_occs ((src, src_macros) : Term.message * MsetAbs.t) ->
        List.fold_left (fun macro_occs (src_macro, mset) -> 
            if Ms.mem src_macro macro_occs 
            then
              let srcs, mset' = Ms.find src_macro macro_occs in
              let new_mset = Mset.join mset mset' in
              Ms.add src_macro (src :: srcs, new_mset) macro_occs
            else Ms.add src_macro ([src], mset) macro_occs
          ) macro_occs src_macros 
      ) Ms.empty sm
  in

  SystemExpr.fold_descrs (fun descr acc ->
      fold_descr ~globals:true (fun msymb is _ t acc ->
          if Ms.mem msymb macro_occs then
            let srcs, mset = Ms.find msymb macro_occs in

            let is' = mset.Mset.msymb.Term.s_indices in
            (* we compute the substitution which we will use to instantiate 
               [t] on the indices of the macro set in [mset]. *)
            let subst = 
              List.map2 (fun i j -> 
                  Term.ESubst (Term.mk_var i, Term.mk_var j)
                ) is is'
            in

            let fv = Sv.diff (Sv.of_list1 is') env in
            let fv = 
              List.map (fun (Vars.EVar v) -> 
                  Vars.cast v Type.KIndex
                ) (Sv.elements fv) 
            in

            let iocc = { 
              iocc_aname   = descr.name;
              iocc_vars    = fv;
              iocc_action  = Action.subst_action subst descr.action;
              iocc_cnt     = Term.subst subst t; 
              iocc_sources = srcs; 
            } in

            let descr () = Action.subst_descr subst descr in

            func descr iocc acc 
          else acc
        ) cntxt.table cntxt.system descr acc
    ) cntxt.table cntxt.system init


(** Same as [fold_macro_support], but without passing the description to [func] *)
let fold_macro_support 
    (func : (iocc -> 'a -> 'a)) 
    (cntxt : Constr.trace_cntxt)
    (env : Vars.env)
    (terms : Term.message list) 
    (init : 'a) : 'a 
  =
  _fold_macro_support (fun _ -> func) cntxt env terms init

(** Less precise version of [fold_macro_support], which does not track sources. *)
let fold_macro_support0 
    (func : (
        Symbols.action Symbols.t -> (* action name *)
        Action.action ->            (* action *)
        Term.message ->             (* term *)
        'a -> 'a)) 
    (cntxt : Constr.trace_cntxt)
    (env : Vars.env)
    (terms : Term.message list) 
    (init : 'a) : 'a 
  =
  _fold_macro_support (fun _ iocc acc ->
      func iocc.iocc_aname iocc.iocc_action iocc.iocc_cnt acc
    ) cntxt env terms init


(** Less precise version of [fold_macro_support], which does not track sources. *)
let fold_macro_support1
    (func : (Action.descr -> Term.message -> 'a -> 'a)) 
    (cntxt : Constr.trace_cntxt)
    (env : Vars.env)
    (terms : Term.message list) 
    (init : 'a) : 'a 
  =
  _fold_macro_support (fun descr iocc acc ->
      func (descr ()) iocc.iocc_cnt acc
    ) cntxt env terms init
