open Utils

(*------------------------------------------------------------------*)
module Pos = Match.Pos
               
module Sv = Vars.Sv

module SE = SystemExpr

module TraceHyps = Hyps.TraceHyps
  
(*------------------------------------------------------------------*)
class deprecated_iter ~(context:ProofContext.t) = object (self)
  method visit_message (t : Term.term) = 
    match t with
    | Term.Int    _
    | Term.String _
    | Fun _ -> ()

    | Tuple l -> List.iter self#visit_message l

    | App (t, l) -> List.iter self#visit_message (t :: l)

    | Proj (_, t) -> self#visit_message t

    | Let (_, t1, t2) -> self#visit_message t1; self#visit_message t2

    | Macro (ms,l,ts) ->
      (* no need to fold over [l] or [ts], since we expand the macro *)
      let res =
        match Macros.unfold context.env ms l ts with
        | `Results bodies ->
          List.fold_left (fun acc x -> x.Macros.out :: x.Macros.when_cond :: acc) [] bodies
        | `Unknown -> assert false
      in
      List.iter self#visit_message res

    | Name _ | Var _ -> ()

    | Diff (Explicit l) ->
      List.iter (fun (_,tm) -> self#visit_message tm) l

    | Find (a, b, c, d) ->
      let _, subst = Term.refresh_vars a in
      let b = Term.subst subst b in
      let c = Term.subst subst c in
      self#visit_message b; self#visit_message c; self#visit_message d

    | Quant (_,vs,l) ->
      let _, subst = Term.refresh_vars vs in
      let l = Term.subst subst l in
      self#visit_message l

    | Term.Action _ -> ()
end

(*------------------------------------------------------------------*)
class ['a] deprecated_fold ~(context:ProofContext.t) = object (self)
  method fold_message (x : 'a) (t : Term.term) : 'a = 
    match t with                      
    | Tuple l -> List.fold_left self#fold_message x l

    | App (t, l) -> List.fold_left self#fold_message x (t :: l)

    | Proj (_, t) -> self#fold_message x t

    | Let (_, t1, t2) ->
      self#fold_message (self#fold_message x t1) t2

    | Macro (ms,l,ts) ->
      (* no need to fold over [l] or [ts], since we expand the macro *)
      let res =
        match Macros.unfold context.env ms l ts with
        | `Results bodies ->
          List.fold_left (fun acc x -> x.Macros.out :: x.Macros.when_cond :: acc) [] bodies
        | `Unknown -> assert false
      in      
      List.fold_left self#fold_message x res

    | Name _ | Var _ -> x

    | Diff (Explicit l) ->
      List.fold_left (fun x (_,tm) -> self#fold_message x tm) x l

    | Find (a, b, c, d) ->
      let _, s = Term.refresh_vars a in
      let b = Term.subst s b in
      let c = Term.subst s c in
      let d = Term.subst s d in
      self#fold_message (self#fold_message (self#fold_message x b) c) d

    | Quant (_,vs,l) ->
      let _, s = Term.refresh_vars vs in
      let l = Term.subst s l in
      self#fold_message x l

    | Term.Int    _
    | Term.String _
    | Term.Fun _
    | Term.Action _ -> x

end

(*------------------------------------------------------------------*)
class deprecated_iter_approx_macros ~exact ~(context:ProofContext.t) = 
  object (self)

  inherit deprecated_iter ~context as super

  val mutable checked_macros = []

  method visit_macro (ms : Term.msymb) (args : Term.terms) (a : Term.term) : unit = 
    match Symbols.get_macro_data ms.s_symb context.env.table with
    | _ when Symbols.is_quantum_macro ms.s_symb ->
      Tactics.soft_failure (Tactics.Failure "quantum macros unsupported")

    | _ when List.mem ms.s_symb Symbols.Classic.[inp; out; cond; exec; frame] -> ()
    (* no implemented, as this is a depracated function *)

    | Symbols.General _ -> assert false (* FIXME: do we need a clean error-message? *)
      
    | Symbols.State _ -> ()
    | Symbols.Global _ ->
      if exact then
        let res =
          match Macros.unfold context.env ms args a with
          | `Results bodies ->
            List.fold_left (fun acc x -> x.Macros.out :: x.Macros.when_cond :: acc) [] bodies
          | `Unknown -> assert false
        in
        List.iter self#visit_message res        
      else if not (List.mem ms.s_symb checked_macros) then begin
        checked_macros <- ms.s_symb :: checked_macros ;
        self#visit_message
          (Macros.get_dummy_definition
             context.env.table
             (SE.to_fset context.env.system.set) ms ~args)
          (* FIXME: to_fset? *)
      end

  method visit_message = function
    | Macro (ms,l,a) -> self#visit_macro ms l a
    | m -> super#visit_message m
end

(*------------------------------------------------------------------*)
class deprecated_get_f_messages ?(drop_head=true)
    ?(fun_wrap_key=None)
    ~(context:ProofContext.t) f k = object (self)
  inherit deprecated_iter_approx_macros ~exact:true ~context as super
  val mutable occurrences : (Term.term list * Term.term) list = []
  method get_occurrences = occurrences
  method visit_message = function
    | Term.App (Fun (f',_), [Tuple [m;k']]) as m_full when f' = f ->
      begin match k' with
        | Term.Name (s', args') when s'.s_symb = k ->
          let ret_m = if drop_head then m else m_full in
          occurrences <- (args', ret_m) :: occurrences
        | _ -> ()
      end ;
      self#visit_message m ; self#visit_message k'

    | Term.App (Fun (f', _), [Tuple [m;_r;k']]) as m_full when f' = f ->
      begin match k', fun_wrap_key with
        | Term.Name (s',args'), None when s'.s_symb = k ->
          let ret_m = if drop_head then m else m_full in
          occurrences <- (args', ret_m) :: occurrences

        | Term.App (Fun (f', _), [Term.Name (s',args')]), Some is_pk
          when is_pk f' && s'.s_symb = k ->
          let ret_m = if drop_head then m else m_full in
          occurrences <- (args', ret_m) :: occurrences

        | _ -> ()
      end ;
      self#visit_message m ; self#visit_message k'

    | Term.Var m when not (Symbols.TyInfo.is_finite context.env.table (Vars.ty m)) ->
      (* TODO: DET: check for ptime_deducible *)
      assert false (* SSC must have been checked first *)

    | m -> super#visit_message m
end

(*------------------------------------------------------------------*)
(** {2 Occurrences} *)
type 'a occ = {
  occ_cnt  : 'a;
  occ_vars : Vars.vars;  (** variables bound above the occ. *)
  occ_cond : Term.terms; (** conditions above the occ. *)
  occ_pos  : Pos.Sp.t;   (** optional, empty if unused *)
}

let pp_occ pp_cnt fmt occ =
  let pp_pos fmt pos =
    if pos = [] then ()
    else
      Fmt.pf fmt " at @[%a@]"
        (Fmt.list ~sep:Fmt.comma Pos.pp) pos
  in
  Fmt.pf fmt "[@[%a@] | ∃@[%a@], @[%a@]%a]"
    pp_cnt occ.occ_cnt
    (Fmt.list ~sep:Fmt.comma Vars.pp) occ.occ_vars
    (Fmt.list ~sep:Fmt.comma Term.pp) occ.occ_cond
    pp_pos (Match.Pos.Sp.elements occ.occ_pos)

type 'a occs = 'a occ list

(** Like [Term.tfold], but also propagate downward (globally refreshed)
    bound variables and conditions.
    If [Mode = `Delta _], try to expand macros before calling [func].
    Over-approximation: we try to expand macros, even if they are at a timestamp
    that may not happen.
    **DEPRECATED**, use [Match.Pos.fold] instead. *)
let tfold_occ (type a)
    ~(mode : [`Delta of ProofContext.t | `NoDelta ])
    (func  : fv:Vars.vars -> cond:Term.terms -> Term.term -> a -> a) 
    ~(fv   : Vars.vars)
    ~(cond : Term.terms)
    (t     : Term.term) 
    (acc   : a) 
  : a 
  =
  match t with
  | Term.Quant (_, evs, t) ->
    let evs, subst = Term.refresh_vars evs in
    let t = Term.subst subst t in
    let fv = List.rev_append evs fv in
    func ~fv ~cond t acc

  | Term.App (Fun (fs, _), [c;t;e]) when fs = Term.f_ite ->
    func ~fv ~cond c acc |>
    func ~fv ~cond:(c :: cond) t |>
    func ~fv ~cond:(Term.mk_not c :: cond) e

  | Term.Let (v,t1,t2) ->
    let v, subst = Term.refresh_vars [v] in
    let t1 = Term.subst subst t1 in
    let t2 = Term.subst subst t2 in
    let v = as_seq1 v in
    
    let fv2 = v :: fv in
    let ceq = Term.mk_eq (Term.mk_var v) t1 in
    
    func ~fv     ~cond               t1 acc |>
    func ~fv:fv2 ~cond:(ceq :: cond) t2 

  | Term.Find (is, c, t, e) ->
    let is, subst = Term.refresh_vars is in
    let c, t = Term.subst subst c, Term.subst subst t in
    let fv1 = List.rev_append is fv in

    let cond_e =
      Term.(mk_not (mk_exists (List.map (fun i -> i) is)  c)) :: cond 
    in

    func ~fv:fv1 ~cond c acc |>
    func ~fv:fv1 ~cond:(c :: cond) t |>
    func ~fv:fv  ~cond:cond_e e

  | Term.Macro (_, l, ts) -> 
    let default s : a = 
      List.fold_left (fun acc t -> func ~fv ~cond t acc) acc s
    in

    begin
      match mode with
      | `NoDelta -> default (l @ [ts])
      | `Delta constr ->
        let res, has_red =
          Match.reduce_delta_macro1
            ~constr:true constr.env ~hyps:constr.hyps t
        in
        if has_red = True then default @@ [res] else default (l @ [ts])     
    end

  | Term.Int    _
  | Term.String _
  | Term.App    _
  | Term.Tuple  _
  | Term.Proj   _
  | Term.Name   _
  | Term.Fun    _
  | Term.Action _
  | Term.Var    _
  | Term.Diff   _ ->
    Term.tfold (func ~fv ~cond) t acc

(*------------------------------------------------------------------*)

(** {2 get_ftype} *)

type mess_occ = Term.term occ

type mess_occs = mess_occ list

type fsymb_matcher =
  | Type of Symbols.OpData.abstract_def
  | Symbol of Symbols.fname

let matching table fn = function
  | Symbol fsymb -> fsymb = fn
  | Type symtype -> Symbols.OpData.is_abstract_with_ftype fn symtype table


(** Looks for occurrences of subterms using a function symbol of the given kind
    (Hash, Dec, ...) or with the given head.
    Does not recurse below terms whose head is excluded by [excludesymtype]. *)
let get_f 
    ?(excludesymtype : Symbols.OpData.abstract_def option)
    ?(allow_diff=false)
    (table           : Symbols.table)
    (symtype         : fsymb_matcher)
    (t               : Term.term)
  : mess_occs 
  =
  let rec get (t : Term.term) ~(fv : Vars.vars) ~(cond : Term.terms) : mess_occs =
    let occs () =
      tfold_occ ~mode:`NoDelta (fun ~fv ~cond t occs ->
          get t ~fv ~cond @ occs
        ) ~fv ~cond t []
    in

    match t with
    | Term.App (Term.Fun (fn,_),_)  ->
      let head_occ =
        if matching table fn symtype
        then [{ occ_cnt  = t;
                occ_vars = List.rev fv;
                occ_cond = cond;
                occ_pos  = Pos.Sp.empty; }]
        else []
      in

      let rec_occs = match excludesymtype with
        | Some ex when Symbols.OpData.is_abstract_with_ftype fn ex table -> []
        | _ -> occs ()
      in

      head_occ @ rec_occs

    | Term.Diff (Explicit l) when allow_diff ->
      let head_occ =
        if List.for_all
             (function
                | (_, Term.App (Fun (f,_),_)) -> matching table f symtype
                | _ -> false)
             l
        then [{ occ_cnt  = t;
                occ_vars = List.rev fv;
                occ_cond = cond;
                occ_pos  = Pos.Sp.empty; }]
        else []
      in
      head_occ @ occs ()

    | _ -> occs ()
  in

  get t ~fv:[] ~cond:[]


let get_ftypes 
    ?(excludesymtype : Symbols.OpData.abstract_def option)
    (table           : Symbols.table)
    (symtype         : Symbols.OpData.abstract_def)
    (t               : Term.term) 
  : mess_occs 
  = 
  get_f ?excludesymtype table (Type symtype) t

let get_fsymb 
    ?(excludesymtype : Symbols.OpData.abstract_def option)
    ?(allow_diff     : bool option)
    (table           : Symbols.table)
    (symtype         : Symbols.fname)
    (t               : Term.term)
  :  mess_occs = 
  get_f ?excludesymtype ?allow_diff table (Symbol symtype) t


(*------------------------------------------------------------------*)
(** {2 get_diff} *)

type diff_occ = Term.term occ

type diff_occs = diff_occ list


(** Looks for occurrences of diff operator.  *)
let get_diff ~(context : ProofContext.t) (t : Term.term) : diff_occs =
  let rec get (t : Term.term) ~(fv:Vars.vars) ~(cond:Term.terms) : diff_occs =
    let occs () =
      tfold_occ ~mode:(`Delta context) (fun ~fv ~cond t occs ->
          get t ~fv ~cond @ occs
        ) ~fv ~cond t []
    in
    match t with
    | Term.Diff _ ->
      [{ occ_cnt  = t;
         occ_vars = List.rev fv;
         occ_cond = cond;
         occ_pos  = Pos.Sp.empty; }]

    | _ -> occs ()
  in

  get t ~fv:[] ~cond:[]


(*------------------------------------------------------------------*)
(** {2 Find [Fun _] applications} *)

(** pair of the key indices and the term *)
type hash_occ = (Term.term list * Term.term) occ

type hash_occs = hash_occ list

let pp_hash_occ fmt (x : hash_occ) =
  pp_occ (fun fmt (kis, m) ->
      Fmt.pf fmt "@[&H(%a, &K(%a))@]"
        Term.pp m
        (Fmt.list ~sep:Fmt.sp Term.pp) kis) fmt x

(*------------------------------------------------------------------*)
(** {2 Folding over action descriptions} *)

(** Fold over macros defined at a given description. *)
let fold_descr
    (func :
       (Symbols.macro ->       (* macro symbol [ms] *)
        Vars.var list ->       (* action indices *)
        args:Term.term list -> (* argument of the macro [ms] for state and globals *)
        body:Term.term ->      (* term [t] defining [ms(is)] *)
        'a ->                  (* folding argument *)
        'a))
    (env    : Env.t)
    (descr  : Action.descr)
    (init   : 'a) : 'a
  =
  let system = SE.to_fset env.system.set in
  let mval =
    let out_symb, cond_symb = 
      match descr.exec_model with
      | Action.Classic     -> Symbols.Classic.out, Symbols.Classic.cond
      | Action.PostQuantum -> Symbols.Quantum.out, Symbols.Quantum.cond
    in
    func out_symb  descr.indices ~args:[] ~body:(snd descr.output   ) init |>
    func cond_symb descr.indices ~args:[] ~body:(snd descr.condition) 
  in

  (* fold over state macros *)
  let mval =
    List.fold_left (fun mval (st, args, t) ->
        func st descr.indices ~args ~body:t mval
      ) mval descr.updates
  in

  (* fold over global macros in scope of [descr.action] *)
  let ts = SE.action_to_term env.table system (Action.to_action descr.action) in
  (* fold over global macros in scope of [descr.action] *)
  List.fold_left (fun mval (mg : Symbols.macro) ->
      let is_arr, _ =
        match Symbols.get_macro_data mg env.table with
        | Global (is,ty,_) -> is, ty
        | _ -> assert false
      in
      let args = Term.mk_vars (List.take is_arr descr.Action.indices) in
      let res =
        let msymb = Macros.msymb env.table mg in
        match Macros.unfold env msymb args ts with
        | `Results bodies ->
          List.fold_left
            (fun acc x -> x.Macros.out :: x.Macros.when_cond :: acc)
            [] bodies
        | `Unknown -> assert false
      in        
      List.fold_left (fun mval t ->
          func mg descr.indices ~args ~body:t mval
        ) mval res        
    ) mval descr.globals

(*------------------------------------------------------------------*)
(** {2 Path conditions} *)

(** See `.mli` *)
module PathCond = struct
  type t =
    | Top                    
    | Before of Action.descr list

  let join (cond1 : t) (cond2 : t) : t =
    match cond1, cond2 with
    | Top, _ | _, Top -> Top
    | Before l1, Before l2 -> 
      Before (List.remove_duplicate (fun d1 d2 -> d1.Action.name = d2.Action.name) (l1 @ l2))

  let pp fmt : t -> unit = function
    | Top -> ()
    | Before l -> 
      Fmt.pf fmt " s.t. τ ≤ [@[%a@]]" 
        (Fmt.list ~sep:Fmt.comma Symbols.pp_path) (List.map (fun d -> d.Action.name) l)

  let incl (p1 : t) (p2 : t) : bool =
    match p1, p2 with
    | _, Top -> true
    | Top, _ -> false
    | Before l1, Before l2 ->
      List.for_all (fun d1 ->
          List.exists (fun d2 -> 
              d1.Action.name = d2.Action.name
            ) l2
        ) l1

  (** Sound approximation of the concatenation of two path conditions. 
      (path [p1] followed by path [p2]) *)
  let concat
      ?(all_actions : Symbols.action list = []) (p1 : t) (p2 : t) : t 
    =
    match p2 with
    | Top -> p1
    (* heuristic: use the last (i.e. right-most) action name which is not [Top] *)
    (* p1 · ⊤ ⇒ p1 *)

    | Before l
      when List.for_all
          (fun a -> List.exists (fun d -> d.Action.name = a) l) 
          all_actions
      ->
      p1
    (* p1 · ⊤ ⇒ p1 *)
    (* same as previous cas *)

   | Before _ -> p2
   (* p1 · p2 ⇒ p2 *)

  let apply table (p : t) (tau0 : Term.term) (tau2 : Term.term) (order : Symbols.fname) : Term.term =
    let mk_leq t1 t2 =
      if Symbols.path_equal order Library.Prelude.fs_lt then
        (* we use the function which automatically replaces t1 <= pred(t) with t1 < tt *)
        Term.mk_timestamp_leq t1 t2
      else
        Term.mk_or
          (Term.mk_fun_infer_tyargs table order [t1; t2])
          (Term.mk_eq t1 t2)
    in
    match p with
    | Top -> mk_leq tau0 tau2
    | Before l -> 
      Term.mk_ors
        (List.map (fun (d : Action.descr) -> 
             let d = Action.refresh_descr d in
             let tau1 = Term.mk_action d.name (List.map Term.mk_var d.indices) in
             Term.mk_exists d.indices 
               (Term.mk_ands [mk_leq tau0 tau1;
                              mk_leq tau1 tau2;])            
           ) l
        )
end

(*------------------------------------------------------------------*)
(** {2 Set of macros} *)

module Sp = Symbols.Sp(Symbols.Macro)
module Mp = Symbols.Mp(Symbols.Macro)

(*------------------------------------------------------------------*)
module Mset : sig[@warning "-32"]
  (** Set of macros over some indices.
        [{ msymb     = m;
           rec_arg_type = ty;
           args;
           indices   = vars; 
           path_cond = φ; }]
      represents the set of terms
        [\{m(args)@τ | ∀ vars, (τ : ty). s.t. (φ τ) \}]. 

      (* TODO: the specification of [path_cond] above is incorrect
      (i.e., [φ] is of type [ty → ty → bool], not [ty → bool]) *)

      It is guaranteed that [vars ∩ env = ∅]. *)
  type t = private {
    msymb        : Term.msymb;
    rec_arg_type : Type.ty;
    args         : Vars.var list;
    indices      : Vars.var list;
    path_cond    : PathCond.t;
  }

  val mk :
    env:Sv.t ->
    rec_arg_type : Type.ty ->    
    msymb:Term.msymb ->
    args:Vars.var list ->
    indices:Vars.var list ->
    path_cond:PathCond.t -> 
    t

  val pp   : t      formatter
  val pp_l : t list formatter

  (** Compute the lub of two msets (w.r.t set inclusion).
      Must be called on sets with the same macro symbol. *)
  val join : t -> t -> t

  (** [mset_incl tbl system s1 s2] check if all terms in [s1] are
      members of [s2]. *)
  val incl : Symbols.table -> SE.fset -> t -> t -> bool
end = struct
  type t = {
    msymb        : Term.msymb;
    rec_arg_type : Type.ty;    
    args         : Vars.var list;
    indices      : Vars.var list;
    path_cond    : PathCond.t;
  }

  let mk ~env ~rec_arg_type ~msymb ~args ~indices ~path_cond : t =
    let indices = Sv.diff (Sv.of_list1 indices) env in
    let indices = Sv.elements indices in
    { msymb; rec_arg_type; args; indices; path_cond; }

  let pp fmt (mset : t) =
    Fmt.pf fmt "@[<hv 2>{ @[%a(%a)@]@@_ |@ %a%a}@]"
      Symbols.pp_path mset.msymb.s_symb
      Vars.pp_list mset.args
      Vars.pp_list mset.indices 
      PathCond.pp mset.path_cond

  let pp_l fmt (mset_l : t list) =
    Fmt.pf fmt "@[<v 0>%a@]"
      (Fmt.list ~sep:Fmt.sp pp) mset_l


  (** Compute the lub of two msets (w.r.t set inclusion).
      Must be called on sets with the same macro symbol.

      A mset is a set of terms of the form:
         [\{m(i₁, ..., iₙ)@τ | ∀ vars, τ \}]
      where [m] is a macro symbol, [τ] is a variable, and
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

    let l = List.length a.args in
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
          let v_a = List.nth a.args i in
          let v_b = List.nth b.args i in

          let univ_var, v =
            match List.mem v_a a.indices, List.mem v_b b.indices with
            | false, false ->
              (* [v_a] and [v_b] are constant w.r.t., resp., [a] and [b]
                 In that case:
                 - if [v_a] = [v_b] then we use [v_a]
                 - otherwise, we must use a fresh universally quantified var. *)
              if v_a = v_b
              then false, v_a
              else true, Vars.make_fresh Type.tindex "i"

            (* [v_a] or [v_b] is not a constant.
               In that case, use a universally quantified variable. *)
            | true, _ -> true, Vars.refresh v_a
            | _, true -> true, Vars.refresh v_b
          in

          (* update [indices_r] *)
          indices_r := if univ_var then v :: !indices_r else !indices_r;

          List.iteri2 (fun j u_a u_b ->
              if u_a = v_a && u_b = v_b then begin
                assert (Array.get arr j = None);
                Array.set arr j (Some v)
              end
            ) a.args b.args
      ) arr;

    let join_is = Array.fold_right (fun a acc -> oget a :: acc) arr [] in
    let join_ms = a_ms in
    assert (Type.equal a.rec_arg_type b.rec_arg_type);
    let path_cond = PathCond.join a.path_cond b.path_cond in
    mk ~env:Sv.empty ~rec_arg_type:a.rec_arg_type
      ~msymb:join_ms ~args:join_is ~path_cond ~indices:(!indices_r)

  let incl table (sexpr : SE.fset) (s1 : t) (s2 : t) : bool =
    let tv = Vars.make_fresh Type.ttimestamp "t" in
    let term1 = Term.mk_macro s1.msymb (Term.mk_vars s1.args) (Term.mk_var tv) in
    let term2 = Term.mk_macro s2.msymb (Term.mk_vars s2.args) (Term.mk_var tv) in

    let pat2 = Term.{ 
        pat_op_term   = term2;
        pat_op_params = Params.Open.empty;
        pat_op_vars   = Vars.Tag.local_vars s2.indices;}
    in
    let system = SE.reachability_context sexpr in
    match
      Match.T.try_match
        ~param:Match.default_param
        table system term1 pat2
    with
    | Match _ -> true
    | NoMatch _ -> false
    (* TODO: we must check for PathCond inclusion here (with a
       [PathCond.incl] most likely *)
end

module MsetAbs : sig[@warning "-32"]
  (** Abstract value containing one mset per macro symbol. *)
  type t = (Symbols.macro * Mset.t) list

  val pp : t formatter

  (** Join a single [mset] into an full abstract value. *)
  val join_single : Mset.t -> t -> t

  (** Join operator. *)
  val join : t -> t -> t

  (** [incl ... abs1 abs2] checks if [abs1 ⊆ abs2]. *)
  val incl : Symbols.table -> SE.fset -> t -> t -> bool

  (** [diff ... abs1 abs2] over-approximates [abs1 \ abs2]. *)
  val diff : Symbols.table -> SE.fset -> t -> t -> t

  val mem : Symbols.macro -> t -> bool
end = struct
  type t = (Symbols.macro * Mset.t) list

  let pp fmt (abs : t) : unit =
    let pp_one fmt (mname, mset) =
      Fmt.pf fmt "@[<h>%a: %a@]" Symbols.pp_path mname Mset.pp mset
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
      (system : SE.fset)
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
      (system : SE.fset)
      (abs1   : t)
      (abs2   : t) : t
    =
    List.filter (fun (mn, m1) ->
        try
          let m2 = List.assoc mn abs2 in
          not (Mset.incl table system m1 m2)
        with Not_found -> true
      ) abs1

  let mem
      (sym : Symbols.macro)
      (abs : t)
    =
    List.mem_assoc sym abs
end

(*------------------------------------------------------------------*)
(** {2 Macros} *)

(** see `.mli` *)
type allowed = NoHonestRand | PTimeSI | PTimeNoSI

(*------------------------------------------------------------------*)
(** occurrences of a macro [n(i,...,j)] *)
type macro_occ_cnt = { symb : Term.msymb; rec_arg_type : Type.ty;  args : Term.term list} 

type macro_occ = macro_occ_cnt occ

type macro_occs = macro_occ list

let default_expand_mode
    (mset : MsetAbs.t) (ms : Term.msymb) (l : Macros.body list) : bool 
  =
  (* The default expand modes expands a macro if we find a single
     definition that successfully matched. *)
  match l with
  | [a] when a.Macros.pattern = None && Term.equal a.when_cond Term.mk_true ->
    (* and if the macro is some fixed list of already explored macros *)
    not(List.mem_assoc ms.s_symb mset)
    (* TODO: this should be replaced by a mset membership tests. 
       [{msymb; args; indices = []; path_c
       ond = Top} ⊆ List.assoc ms mset]

       Note: the role of [path_cond] needs to be clarified
    *)
  | _ -> false

(*------------------------------------------------------------------*)
let update_context
    ~(extra_vars : Vars.vars) (system : SE.context) 
    (context : ProofContext.t)
  : ProofContext.t
  =
  let vars = Vars.add_vars (Vars.Tag.global_vars ~const:true extra_vars) context.env.vars in
  let env = Env.update ~vars context.env in
  ProofContext.make ~env ~hyps:context.hyps |>
  ProofContext.change_system ~system 
  (* need to call [change_system] separately, to properly deal with
     hypotheses *)

(*------------------------------------------------------------------*)
(** Internal. 
    Looks for macro occurrences in a term.  

    Unfold (and thus ignores and does not consider as an occurences)
    some macros, depending on the strategy defined by [expand_mode].

    @raise a user-level error if a non-ptime term variable occurs in the term. *)
let get_macro_occs
    ~(mode  : allowed )   (* allowed sub-terms without further checks *)
    ?(expand_mode : 
        MsetAbs.t -> Term.msymb -> Macros.body list -> bool = default_expand_mode)
    ?(explored_mset : MsetAbs.t = [])
    ~(context : ProofContext.t)      (* initial proof-context *)
    ~(fv      : Vars.vars)           (* additional [fv] not in [context.env.vars] *)
    (t        : Term.term)
  : macro_occs
  =  
  (* TODO: system: this function may recurse below diff-operators
     without changing the system ([system] in [update_context] should
     depend on the precise subterm) *)
  let rec get (t : Term.term) ~(fv : Vars.vars) ~(cond : Term.terms) : macro_occs =
    let context = update_context ~extra_vars:fv context.env.system context in
    let env = context.env in
    assert (Sv.subset (Term.fv t) (Vars.to_vars_set env.vars));

    (* Put [t] in weak head normal form w.r.t. rules in [Reduction.rp_crypto].

       Must be synchronized with corresponding code in
       [Occurrences.get_actions_ext],
       [Occurrences.fold_bad_occs]
       [Crypto]. *)
    let t =
      let red_param = Reduction.rp_crypto in
      let st = Reduction.mk_state context ~red_param in
      let strat = Reduction.(MayRedSub rp_full) in
      fst (Reduction.whnf_term ~strat st t)
    in
    match t with
    | _ when mode = PTimeSI   && HighTerm.is_ptime_deducible ~si:true  env t -> []
    | _ when mode = PTimeNoSI && HighTerm.is_ptime_deducible ~si:false env t -> []
    | _ when mode = NoHonestRand &&
             (HighTerm.is_constant env t ||
              HighTerm.is_ptime_deducible ~si:false env t) -> []

    | Term.Var v -> 
      let err_str =
        Fmt.str "terms contain a %s: @[%a@]" 
          (match mode with
             NoHonestRand -> "variable that may depend on honest randomness"
           | PTimeSI | PTimeNoSI -> "non-ptime variable")
          Vars.pp v
      in
      Tactics.soft_failure (Tactics.Failure err_str)

    | Term.Macro (ms, l, ts) ->
      begin
        (* We try to unfold the corresponding macro.  Here, unfolding
           a macro means that no indirect occurence will be created
           for it. As such, we must expand only when we are sure that
           Occurences.expand_check_once will also be able to expand
           the macro and explore it.  *)
        match Macros.unfold env ms l ts with
        | `Results res when expand_mode explored_mset ms res ->
          (* If we do unfold and the unfolding satisfies the chosen
             expansion mode, we go through alll possible
             expansions. *)
          List.fold_left (fun acc body ->
              begin
                match body.Macros.pattern with
                | None ->
                  (* For each macro, if there is no pattern matching,
                     we recurse over the condition and the out result
                     of the macro. With the default expand mode, we
                     always take this path *)
                  get body.Macros.when_cond ~fv ~cond
                  @ get body.Macros.out ~fv ~cond:(body.when_cond :: cond)
                  @ acc
                | Some pat ->
                  (* If there is a pattern, we must create the
                     corresponding new variables, and then recurse. *)
                  let evs, subst = Term.refresh_vars body.Macros.vars in
                  let mout = Term.subst subst body.out in
                  let mcond = Term.subst subst body.when_cond in
                  let cond_pat = Term.mk_eq ts (Term.subst subst pat) in               
                  let fv = List.rev_append evs fv in
                  get mcond ~fv ~cond:(cond_pat :: cond)
                  @ get mout ~fv ~cond:(cond_pat :: mcond :: cond)
                  @ acc                  
              end
            ) [] res
        | _ ->
          { occ_cnt  = { symb = ms; rec_arg_type = Term.ty ts; args = l; } ;
            occ_vars = List.rev fv;
            occ_cond = cond;
            occ_pos  = Pos.Sp.empty; } ::
          rec_strict_subterms t ~fv ~cond
      end
    | _ -> rec_strict_subterms t ~fv ~cond

  and rec_strict_subterms
      (t : Term.term) ~(fv:Vars.vars) ~(cond:Term.terms) : macro_occs
    =
    (* TODO: replace this tfold_occ by Match.Pos.fold? or other function?*)
    tfold_occ ~mode:`NoDelta
      (fun ~fv ~cond t occs ->
         get t ~fv ~cond @ occs
      ) ~fv ~cond t []
  in
  get t ~fv ~cond:[]


(*------------------------------------------------------------------*)
(** Given a macro occurrence [occ], compute a [Mset.t] value that 
    abstracts it:
    - over-approximations occur whenever the macro occurrence is indexed by 
      complex terms (i.e. not variables). *)
let mset_of_macro_occ (env : Sv.t) ~(path_cond : PathCond.t) (occ : macro_occ) : Mset.t =
  let indices = 
    List.map (function
        | Term.Var v -> v
        | _ as t -> Vars.make_fresh (Term.ty t) "i" 
        (* over-approximation, replacing the term by an fresh variable *)
        (* FEATURE: a more complex abstract domain could do more here *)
      ) occ.occ_cnt.args 
  in
  Mset.mk ~env ~rec_arg_type:occ.occ_cnt.rec_arg_type
    ~msymb:occ.occ_cnt.symb ~args:indices ~indices ~path_cond

(*------------------------------------------------------------------*)
(** Return an over-approximation of the macros reachable from a term
    in any trace model. 
    [macro_support ~mode ~env ~hyps cntxt init = mset1, mset2], 
    where [mset1] is a list of macros occurences directly occuring when
    unfolding the [init] term, and [mset2] is such that:

    unfolding anyone in [mset2] only yields macro occurences already in [mset2]
    [mset1] is included in [mset2] 
*)
let macro_support
    ~(mode : allowed)             (* allowed sub-terms without further checks *)
    ~(context : ProofContext.t)   (* initial proof-context *)
    (term  : Term.term)
  : MsetAbs.t * MsetAbs.t
  =
  let env = context.env in
  let table = env.table in
  let system = SE.to_fset env.system.set in

  (* [get_msymbs] returns the [mset] of all macros occurences inside the
     given term.  It does so by collecting all the occurences, then
     turn each into an mset, then merges them.
  *)
  let get_msymbs
      ~(path_cond   : PathCond.t)
      ~(fv          : Vars.vars)  (* additional [fv] not in [env.vars] *)
      (term         : Term.term) 
    : MsetAbs.t 
    = 
    assert (Sv.subset (Term.fv term) (Sv.union (Vars.to_vars_set env.vars) (Sv.of_list fv)));

    let occs = get_macro_occs ~mode ~context ~fv term in
    let msets =
      List.map (mset_of_macro_occ (Vars.to_vars_set env.vars) ~path_cond) occs
    in
    List.fold_left (fun abs mset -> MsetAbs.join_single mset abs) [] msets
  in
  
  let (init : MsetAbs.t) = get_msymbs ~path_cond:Top ~fv:[] term in
  (* This is only used to update the path conditions, there is probably a better way to do so. *)
  let all_actions : Symbols.action list = 
    SE.fold_descrs (fun d l -> d.name :: l) table system []
  in

  let do1 (sm : MsetAbs.t) : MsetAbs.t =
    List.fold_left (fun acc ((_,mset) : _ * Mset.t) ->       
        let tv_var = Vars.make_fresh mset.rec_arg_type "tau" in
        let tv = Term.mk_var tv_var in
        match
          Macros.unfold env mset.msymb (Term.mk_vars mset.args) tv 
        with
        | `Results res ->
          List.fold_left (fun acc (obody : Macros.body) ->
              let body : Macros.body = Macros.refresh_body obody in
              match body.pattern with
              | None ->
                (* If there is no matching, then we simply collect the
                   new_occs and join everything. *)
                let get_new_occ t =
                  (* We keep the [path_cond] unchanged as there is no pattern. *)
                  get_msymbs ~path_cond:mset.path_cond ~fv:(tv_var :: mset.args @ mset.indices) t
                in
                MsetAbs.join
                  (get_new_occ @@ 
                   Term.mk_ite
                     body.when_cond
                     body.out
                     (Library.Prelude.mk_witness table ~ty_arg:(Term.ty body.out)))
                  acc

              | Some pat ->
                let fv = List.rev_append body.vars (tv_var :: mset.args @ mset.indices) in
                let new_path_cond =
                  match Term.destr_action pat with
                  | None -> mset.path_cond
                  (* FIXME: [path_cond] should become 
                     [PathCond.join mset.path_cond (new_pat = body.pattern)] *)
                  | Some  (asymb, tl) -> 
                    let act = Action.of_term asymb tl table in
                    let descr, subst = SE.descr_of_action table system act in
                    PathCond.concat ~all_actions
                      (PathCond.Before [Action.subst_descr subst descr]) mset.path_cond 
                in
                let get_new_occ t =
                  get_msymbs ~path_cond:new_path_cond ~fv t
                in          
                MsetAbs.join
                  (get_new_occ @@
                   Term.mk_ite
                     body.when_cond
                     body.out
                     (Library.Prelude.mk_witness table ~ty_arg:(Term.ty body.out)))
                  acc                                    
            ) acc res
        | `Unknown -> assert false (* FIXME: use a soft failure  *)
      ) sm sm
  in

  let abs_incl = MsetAbs.incl table system in
  let s_reach = Utils.fpt abs_incl do1 init in

  init, s_reach
  

(*------------------------------------------------------------------*)
(** See `.mli` *)
type iocc = {
  iocc_fun     : Symbols.macro;
  iocc_vars    : Sv.t;
  iocc_rec_arg : Term.term;

  iocc_cond    : Term.term;
  iocc_cnt     : Term.term;

  (* iocc_se      : SE.t; *)

  iocc_sources : Term.term list;
  (* FIXME: replace by a list of (Symbols.macro * Term.term), instead
     of computing this list in a second time *)
  iocc_path_cond : PathCond.t;
  iocc_explored_macros : MsetAbs.t  
}

let pp_iocc fmt (o : iocc) : unit =
  Fmt.pf fmt "@[<v 2>[@[%a@%a@]:@;cnt: @[%a@]@;sources: @[%a@]@;fv: @[%a@]]@]"
    Symbols.pp_path o.iocc_fun
    Term.pp o.iocc_rec_arg
    Term.pp o.iocc_cnt
    (Fmt.list ~sep:Fmt.comma Term.pp) o.iocc_sources
    (Fmt.list ~sep:Fmt.comma Vars.pp) (Sv.elements o.iocc_vars)

(** Folding over all macro descriptions reachable from some terms.
    [env] must contain the free variables of [terms]. 
    See `.mli` for a complete description. *)
let fold_macro_support
    ?(mode : allowed = PTimeSI)   (* allowed sub-terms without further checks *)
    (func  : (iocc -> 'a -> 'a))
    (context : ProofContext.t) (* initial proof-context *)
    (terms : Term.term list)
    (init  : 'a) : 'a
  =
  let env = context.env in
  let table = env.table in
  let venv = Vars.to_vars_set env.vars in

  (* association list of terms and their macro support *)
  let direct_sm, (indirect_sm : (Term.term * MsetAbs.t) list) =
    List.fold_left (fun (dir_acc, ind_acc) src ->
        let directs, indirects = macro_support ~mode ~context src in
        ((src,directs)::dir_acc, (src,indirects)::ind_acc) 
      )
      ([], []) terms
  in

  let mset_indirects = 
    List.fold_left (fun acc (_,mset) -> MsetAbs.join acc mset)
      []
      indirect_sm
  in
  if TConfig.debug_macros table then
    (List.iter (fun (sr, mset_abs) -> 
         Fmt.epr "indirect macro_support of source %a :@.%a@." 
           Term.pp_dbg sr MsetAbs.pp mset_abs
       ) indirect_sm;
     List.iter (fun (sr, mset_abs) -> 
         Fmt.epr "direct macro_support of source %a :@.%a@." 
           Term.pp_dbg sr MsetAbs.pp mset_abs 
       ) direct_sm);

  (* reversing the association map: we want to map macros to
     pairs of possible sources and macro set *)
  let macro_ind_occs : (Term.term list * Mset.t) Mp.t =
    List.fold_left (fun macro_occs ((src, src_macros) : Term.term * MsetAbs.t) ->
        List.fold_left (fun macro_occs (src_macro, mset) ->
            if Mp.mem src_macro macro_occs
            then
              let srcs, mset' = Mp.find src_macro macro_occs in
              let new_mset = Mset.join mset mset' in
              Mp.add src_macro (src :: srcs, new_mset) macro_occs
            else Mp.add src_macro ([src], mset) macro_occs
          ) macro_occs src_macros
      ) Mp.empty indirect_sm
  in 

  List.fold_left
    (fun acc (_, ((srcs, mset) : _ * Mset.t)) ->
       let tv_var = Vars.make_fresh mset.rec_arg_type "t" in
       let tv = Term.mk_var tv_var in 
       match Macros.unfold env mset.msymb (Term.mk_vars mset.args) tv with
       | `Results res ->
         List.fold_left (fun acc (obody : Macros.body) ->
             let (body : Macros.body) = Macros.refresh_body obody in
             let iocc_rec_arg = (odflt tv body.pattern) in

             let out_iocc_vars = 
               Sv.diff (Term.fv (Term.mk_tuple [body.out; body.when_cond; iocc_rec_arg]))
                 venv
             in

             let iocc_out = {
                 iocc_fun             = mset.msymb.s_symb;                
                 iocc_vars            = out_iocc_vars;
                 iocc_rec_arg;                                           
                 iocc_cnt             = body.out;
                 iocc_cond            = body.when_cond;
                 iocc_sources         = srcs;
                 iocc_path_cond       = mset.path_cond;
               (* TODO: here, path_cond could have been built in a smarter
                  way, accumulating the when_cond of all macros on the
                  path. *)
                 iocc_explored_macros = mset_indirects;
             } in
             if TConfig.debug_macros table then
               Printer.prt `Default "@.ioccout: %a@." pp_iocc iocc_out;
             func iocc_out acc
           )
           acc res
       | `Unknown -> assert false
    )
    init
    (Mp.bindings macro_ind_occs)


(** Less precise version of [fold_macro_support], which does not track 
    sources. *)
let fold_macro_support1
    ?(mode : allowed option)   (* allowed sub-terms without further checks *)
    (func  : (Term.term-> Term.term -> 'a -> 'a))
    (context : ProofContext.t) (* initial proof-context *)
    (terms : Term.term list)
    (init  : 'a) : 'a
  =
  fold_macro_support ?mode (fun iocc acc ->
      func iocc.iocc_rec_arg iocc.iocc_cnt acc
    ) context terms init
