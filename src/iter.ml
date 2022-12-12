open Utils

module Pos = Match.Pos
               
module Sv = Vars.Sv
module Sp = Pos.Sp

module SE = SystemExpr

let pp_dbg = false
  
(*------------------------------------------------------------------*)
class deprecated_iter ~(cntxt:Constr.trace_cntxt) = object (self)
  method visit_message (t : Term.term) = 
    match t with
    | Tuple l
    | Fun (_, _,l) -> List.iter self#visit_message l

    | App (t, l) -> List.iter self#visit_message (t :: l)

    | Proj (_, t) -> self#visit_message t

    | Macro (ms,l,ts) ->
      (* no need to fold over [l] or [ts], since we expand the macro *)
      begin
        match Macros.get_definition cntxt ms ~args:l ~ts with
        | `Undef | `MaybeDef -> assert false
        | `Def t -> self#visit_message t
      end

    | Name _ | Var _ -> ()

    | Diff (Explicit l) ->
      List.iter (fun (_,tm) -> self#visit_message tm) l

    | Find (a, b, c, d) ->
      let _, subst = Term.refresh_vars `Global a in
      let b = Term.subst subst b in
      let c = Term.subst subst c in
      self#visit_message b; self#visit_message c; self#visit_message d

    | Quant (_,vs,l) ->
      let _, subst = Term.refresh_vars `Global vs in
      let l = Term.subst subst l in
      self#visit_message l

    | Term.Action _ -> ()
end

(*------------------------------------------------------------------*)
class ['a] deprecated_fold ~(cntxt:Constr.trace_cntxt) = object (self)
  method fold_message (x : 'a) (t : Term.term) : 'a = 
    match t with
    | Tuple l
    | Fun (_, _,l) -> List.fold_left self#fold_message x l

    | App (t, l) -> List.fold_left self#fold_message x (t :: l)

    | Proj (_, t) -> self#fold_message x t

    | Macro (ms,l,ts) ->
      (* no need to fold over [l] or [ts], since we expand the macro *)
      let t = match Macros.get_definition cntxt ms ~args:l ~ts with
        | `Undef | `MaybeDef -> assert false
        | `Def t -> t
      in
      self#fold_message x t

    | Name _ | Var _ -> x

    | Diff (Explicit l) ->
      List.fold_left (fun x (_,tm) -> self#fold_message x tm) x l

    | Find (a, b, c, d) ->
      let _, s = Term.refresh_vars `Global a in
      let b = Term.subst s b in
      let c = Term.subst s c in
      let d = Term.subst s d in
      self#fold_message (self#fold_message (self#fold_message x b) c) d

    | Quant (_,vs,l) ->
      let _, s = Term.refresh_vars `Global vs in
      let l = Term.subst s l in
      self#fold_message x l

    | Term.Action _ -> x

end

(*------------------------------------------------------------------*)
class deprecated_iter_approx_macros ~exact ~(cntxt:Constr.trace_cntxt) = 
  object (self)

  inherit deprecated_iter ~cntxt as super

  val mutable checked_macros = []

  method visit_macro (ms : Term.msymb) (args : Term.terms) (a : Term.term) : unit = 
    match Symbols.Macro.get_def ms.s_symb cntxt.table with
    | Symbols.(Input | Output | State _ | Cond | Exec | Frame) -> ()
    | Symbols.Global _ ->
      if exact then
        match Macros.get_definition cntxt ms ~args ~ts:a with
        | `Def def -> self#visit_message def
        | `Undef | `MaybeDef -> ()
        (* TODO: this may not always be the correct behavior. Check that
           all callees respect this convention *)

      else if not (List.mem ms.s_symb checked_macros) then begin
        checked_macros <- ms.s_symb :: checked_macros ;
        self#visit_message
          (Macros.get_dummy_definition cntxt.table cntxt.system ms ~args)
      end

  method visit_message = function
    | Macro (ms,l,a) -> self#visit_macro ms l a
    | m -> super#visit_message m
end

(*------------------------------------------------------------------*)
class deprecated_get_f_messages ?(drop_head=true)
    ?(fun_wrap_key=None)
    ~(cntxt:Constr.trace_cntxt) f k = object (self)
  inherit deprecated_iter_approx_macros ~exact:true ~cntxt as super
  val mutable occurrences : (Term.term list * Term.term) list = []
  method get_occurrences = occurrences
  method visit_message = function
    | Term.Fun (f',_, [Tuple [m;k']]) as m_full when f' = f ->
      begin match k' with
        | Term.Name (s', args') when s'.s_symb = k ->
          let ret_m = if drop_head then m else m_full in
          occurrences <- (args', ret_m) :: occurrences
        | _ -> ()
      end ;
      self#visit_message m ; self#visit_message k'

    | Term.Fun (f', _,[Tuple [m;_r;k']]) as m_full when f' = f ->
      begin match k', fun_wrap_key with
        | Term.Name (s',args'), None when s'.s_symb = k ->
          let ret_m = if drop_head then m else m_full in
          occurrences <- (args', ret_m) :: occurrences

        |Term.Fun (f', _, [Term.Name (s',args')]), Some is_pk
          when is_pk f' && s'.s_symb = k ->
          let ret_m = if drop_head then m else m_full in
          occurrences <- (args', ret_m) :: occurrences

        | _ -> ()
      end ;
      self#visit_message m ; self#visit_message k'

    | Term.Var m when not (Type.is_finite (Vars.ty m)) ->
      assert false (* SSC must have been checked first *)

    | m -> super#visit_message m
end

(*------------------------------------------------------------------*)
(** {2 Occurrences} *)
type 'a occ = {
  occ_cnt  : 'a;
  occ_vars : Vars.vars;  (** variables bound above the occ. *)
  occ_cond : Term.terms; (** conditions above the occ. *)
  occ_pos  : Sp.t;       (** optional, empty if unused *)
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
    ~(mode : [`Delta of Constr.trace_cntxt | `NoDelta ])
    (func  : fv:Vars.vars -> cond:Term.terms -> Term.term -> a -> a) 
    ~(fv   : Vars.vars)
    ~(cond : Term.terms)
    (t     : Term.term) 
    (acc   : a) 
  : a 
  =
  match t with
  | Term.Quant (_, evs, t) ->
    let evs, subst = Term.refresh_vars `Global evs in
    let t = Term.subst subst t in
    let fv = List.rev_append evs fv in
    func ~fv ~cond t acc

  | Term.Fun (fs, _, [c;t;e]) when fs = Term.f_ite ->
    func ~fv ~cond c acc |>
    func ~fv ~cond:(c :: cond) t |>
    func ~fv ~cond:(Term.mk_not c :: cond) e

  | Term.Find (is, c, t, e) ->
    let is, subst = Term.refresh_vars `Global is in
    let c, t = Term.subst subst c, Term.subst subst t in
    let fv1 = List.rev_append is fv in

    let cond_e =
      Term.(mk_not (mk_exists (List.map (fun i -> i) is)  c)) :: cond 
    in

    func ~fv:fv1 ~cond c acc |>
    func ~fv:fv1 ~cond:(c :: cond) t |>
    func ~fv:fv  ~cond:cond_e e

  | Term.Macro (m, l, ts) -> 
    let default () : a = 
      List.fold_left (fun acc t -> func ~fv ~cond t acc) acc (l @ [ts])
    in

    begin
      match mode with
      | `NoDelta -> default ()
      | `Delta constr ->
        match Macros.get_definition constr m ~args:l ~ts with
        | `Def t -> func ~fv ~cond t acc
        | `Undef | `MaybeDef -> default ()
    end

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
(** Try to unfold a macro.
    To be used in conjunction with [Match.Pos.map_fold]. *)
let try_unfold cntxt (m : Term.msymb) ~(args : Term.terms) ~(ts : Term.term) acc =
  match Macros.get_definition cntxt m ~args ~ts with
  | `Def t             -> acc, `Map t
  | `Undef | `MaybeDef -> acc, `Continue

(*------------------------------------------------------------------*)
(** {2 get_ftype} *)

type mess_occ = Term.term occ

type mess_occs = mess_occ list

type fsymb_matcher =
  | Type of Symbols.function_def
  | Symbol of Symbols.fname

let matching table fn = function
  | Symbol fsymb -> fsymb = fn
  | Type symtype -> Symbols.is_ftype fn symtype table


(** Looks for occurrences of subterms using a function symbol of the given kind
    (Hash, Dec, ...) or with the given head.
    Does not recurse below terms whose head is excluded by [excludesymtype]. *)
let get_f 
    ?(excludesymtype : Symbols.function_def option)
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
    | Term.Fun (fn,_,_)  ->
      let head_occ =
        if matching table fn symtype
        then [{ occ_cnt  = t;
                occ_vars = List.rev fv;
                occ_cond = cond;
                occ_pos  = Sp.empty; }]
        else []
      in

      let rec_occs = match excludesymtype with
        | Some ex when Symbols.is_ftype fn ex table -> []
        | _ -> occs ()
      in

      head_occ @ rec_occs

    | Term.Diff (Explicit l) when allow_diff ->
      let head_occ =
        if List.for_all
             (function
                | (_, Term.Fun (f,_,_)) -> matching table f symtype
                | _ -> false)
             l
        then [{ occ_cnt  = t;
                occ_vars = List.rev fv;
                occ_cond = cond;
                occ_pos  = Sp.empty; }]
        else []
      in
      head_occ @ occs ()

    | _ -> occs ()
  in

  get t ~fv:[] ~cond:[]


let get_ftypes 
    ?(excludesymtype : Symbols.function_def option)
    (table           : Symbols.table)
    (symtype         : Symbols.function_def)
    (t               : Term.term) 
  : mess_occs 
  = 
  get_f ?excludesymtype table (Type symtype) t

let get_fsymb 
    ?(excludesymtype : Symbols.function_def option)
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
let get_diff ~(cntxt : Constr.trace_cntxt) (t : Term.term) : diff_occs =
  let rec get (t : Term.term) ~(fv:Vars.vars) ~(cond:Term.terms) : diff_occs =
    let occs () =
      tfold_occ ~mode:(`Delta cntxt) (fun ~fv ~cond t occs ->
          get t ~fv ~cond @ occs
        ) ~fv ~cond t []
    in
    match t with
    | Term.Diff _ ->
      [{ occ_cnt  = t;
         occ_vars = List.rev fv;
         occ_cond = cond;
         occ_pos  = Sp.empty; }]

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
(** [get_f_messages_ext ~cntxt f k t] collects direct occurrences of
    [f(_,k(_))] or [f(_,_,k(_))] where [f] is a function name [f] and [k] 
    a name [k].
    Over-approximation: we try to expand macros, even if they are at a 
    timestamp that may not happen. *)
let get_f_messages_ext 
    ?(drop_head    = true)
    ?(fun_wrap_key = None)
    ?(fv    : Vars.vars = [])
    ~(mode:[`Delta of Constr.trace_cntxt | `NoDelta])
    (sexpr  : SE.arbitrary)
    (f      : Symbols.fname)
    (k      : Symbols.name)
    (t      : Term.term)
  : hash_occs
  =
  let init_fv = fv in
  
  let func : hash_occs Pos.f_map_fold = fun
    (t : Term.term)
    (se : SE.arbitrary) (fv : Vars.vars) (cond : Term.terms) pos
    (occs : hash_occs) ->
    match t with
      | Term.Fun (f',_, [Tuple [m;k']]) as m_full when f' = f ->
        let occs' =
          match k' with
          | Term.Name (s', args') when s'.s_symb = k ->
            let ret_m = if drop_head then m else m_full in
            [{ occ_cnt  = args', ret_m;
               occ_vars = init_fv @ (List.rev fv);
               occ_cond = cond;
               occ_pos  = Sp.singleton pos; }]
          | _ -> []
        in
        occs' @ occs, `Continue

      | Term.Fun (f', _, [Tuple [m;_r;k']]) as m_full when f' = f ->
        let occs' =
          match k', fun_wrap_key with
          | Term.Name (s', args'), None when s'.s_symb = k ->
            let ret_m = if drop_head then m else m_full in
            [{ occ_cnt  = args', ret_m;
               occ_vars = init_fv @ (List.rev fv);
               occ_cond = cond;
               occ_pos  = Sp.singleton pos; }]

          |Term.Fun (f', _, [Term.Name (s', args')]), Some is_pk
            when is_pk f' && s'.s_symb = k ->
            let ret_m = if drop_head then m else m_full in
            [{ occ_cnt  = args', ret_m;
               occ_vars = init_fv @ (List.rev fv);
               occ_cond = cond;
               occ_pos  = Sp.singleton pos; }]
          | _ -> []
        in
        occs' @ occs, `Continue

      | Term.Var m when not (Type.is_finite (Vars.ty m)) -> assert false
      (* SSC must have been checked first *)

      | Term.Macro (m, l, ts) ->
        begin
          match mode with 
          | `Delta cntxt ->
            let cntxt = { cntxt with system = SE.to_fset se } in
            try_unfold cntxt m ~args:l ~ts occs
          | `NoDelta -> occs, `Continue
        end
        
      | _ -> occs, `Continue
  in

  let occs, _, _ =
    Pos.map_fold ~mode:(`TopDown true) func sexpr [] t
  in
  occs


(*------------------------------------------------------------------*)
(** {2 Macros} *)

(** occurrences of a macro [n(i,...,j)] *)
type macro_occ_cnt = { symb : Term.msymb; args : Term.term list} 

type macro_occ = macro_occ_cnt occ

type macro_occs = macro_occ list

exception Var_found

(** Looks for macro occurrences in a term.
    - [mode = `FullDelta]: all macros that can be expanded are ignored.
    - [mode = `Delta]: only Global macros are expanded (and ignored)
    @raise Var_found if a term variable occurs in the term. *)
let get_macro_occs  
    ~(mode  : [`FullDelta | `Delta ])
    (constr : Constr.trace_cntxt)
    (t      : Term.term)
  : macro_occs
  =
  let rec get (t : Term.term) ~(fv:Vars.vars) ~(cond:Term.terms) : macro_occs =
    match t with
    | Term.Var v when not (Type.is_finite (Vars.ty v)) ->
      raise Var_found

    | Term.Macro (ms, l, ts) ->
      let default () =
        { occ_cnt  = { symb = ms; args = l; } ;
          occ_vars = List.rev fv;
          occ_cond = cond;
          occ_pos  = Sp.empty; } ::
        rec_strict_subterms t ~fv ~cond
      in

      if mode = `FullDelta || Macros.is_global constr.table ms.Term.s_symb then
        match Macros.get_definition constr ms ~args:l ~ts with
        | `Def t -> get t ~fv ~cond
        | `Undef | `MaybeDef -> default ()
      else default ()

    | _ -> rec_strict_subterms t ~fv ~cond

  and rec_strict_subterms
      (t : Term.term) ~(fv:Vars.vars) ~(cond:Term.terms) : macro_occs
    = 
    tfold_occ ~mode:`NoDelta
      (fun ~fv ~cond t occs ->
         get t ~fv ~cond @ occs
      ) ~fv ~cond t []
  in
  get t ~fv:[] ~cond:[]


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
        (Fmt.list ~sep:Fmt.comma Symbols.pp) (List.map (fun d -> d.Action.name) l)

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

    | Before l
      when List.for_all (fun a -> List.exists (fun d -> d.Action.name = a) l) all_actions -> 
      p1
    (* same as previous cas *)

   | Before _ -> p2

  let apply (p : t) (tau0 : Term.term) (tau2 : Term.term) : Term.term =
    match p with
    | Top -> Term.mk_timestamp_leq tau0 tau2
    | Before l -> 
      Term.mk_ors
        (List.map (fun (d : Action.descr) -> 
             let d = Action.refresh_descr d in
             let tau1 = Term.mk_action d.name (List.map Term.mk_var d.indices) in
             Term.mk_exists d.indices 
               (Term.mk_ands [Term.mk_timestamp_leq tau0 tau1;
                              Term.mk_timestamp_leq tau1 tau2;])
           ) l
        )
end

(*------------------------------------------------------------------*)
(** {2 Folding over action descriptions} *)

let is_state : Symbols.macro_def -> bool = function
  | Symbols.State _ -> true
  | _ -> false

(** Fold over macros defined at a given description.
    Also folds over global macros if [globals] is [true]. *)
let fold_descr
    ~(globals:bool)
    (func :
       Symbols.macro ->       (* macro symbol [ms] *)
       Vars.var list ->       (* action indices *)
       Vars.var list ->       (* additional indices [is] of [ms] *)
       Symbols.macro_def ->   (* macro definition *)
       Term.term ->           (* term [t] defining [ms(is)] *)
       'a ->                  (* folding argument *)
       'a)
    (table  : Symbols.table)
    (system : SE.fset)
    (descr  : Action.descr)
    (init   : 'a) : 'a
  =
  let mval = func Symbols.out  descr.indices [] Symbols.Output (snd descr.output   ) init in
  let mval = func Symbols.cond descr.indices [] Symbols.Cond   (snd descr.condition) mval in

  (* fold over state macros *)
  let mval =
    List.fold_left (fun mval (st, is, t) ->
        let mdef = Symbols.Macro.get_def st table in
        assert (is_state mdef);
        func st descr.indices is mdef t mval
      ) mval descr.updates
  in

  if not globals then mval
  else
    let ts = SE.action_to_term table system (Action.to_action descr.action) in
    let cntxt = Constr.{ system; table; models = None; } in

    (* fold over global macros in scope of [descr.action] *)
    List.fold_left (fun mval (mg : Symbols.macro) ->
        let mdef, is_arr, ty = match Symbols.Macro.get_def mg table with
          | Global (is,ty) as mdef -> mdef, is, ty
          | _ -> assert false
        in
        let is = List.take is_arr descr.Action.indices in
        let t = 
          let msymb = Term.mk_symb mg ty in
          let args = Term.mk_vars is in
          match Macros.get_definition cntxt msymb ~args ~ts with
          | `Def t -> t
          | _ -> assert false
        in
        func mg descr.indices is mdef t mval
      ) mval descr.globals

(*------------------------------------------------------------------*)
module Ss = Symbols.Ss(Symbols.Macro)
module Ms = Symbols.Ms(Symbols.Macro)

let is_glob table ms =
  match Symbols.Macro.get_def ms table with
  | Symbols.Global _ -> true
  | _ -> false

(*------------------------------------------------------------------*)
module Mset : sig[@warning "-32"]
  (** Set of macros over some indices.
        [{ msymb     = m;
           args;
           indices   = vars; 
           path_cond = φ; }]
      represents the set of terms [\{m(args)@τ | ∀ vars, τ s.t. (φ τ) \}]. 

      It is guaranteed that [vars ∩ env = ∅]. *)
  type t = private {
    msymb     : Term.msymb;
    args      : Vars.var list;
    indices   : Vars.var list;
    path_cond : PathCond.t;
  }

  val mk :
    env:Sv.t ->
    msymb:Term.msymb ->
    args:Vars.var list ->
    indices:Vars.var list ->
    path_cond:PathCond.t -> 
    t

  val pp   : Format.formatter -> t      -> unit
  val pp_l : Format.formatter -> t list -> unit

  (** Compute the lub of two msets (w.r.t set inclusion).
      Must be called on sets with the same macro symbol. *)
  val join : t -> t -> t

  (** [mset_incl tbl system s1 s2] check if all terms in [s1] are
      members of [s2]. *)
  val incl : Symbols.table -> SE.fset -> t -> t -> bool

  (** Simple mset builder, when the macro symbol is not indexed. *)
  val mk_simple : Symbols.macro -> Type.ty -> t
end = struct
  type t = {
    msymb     : Term.msymb;
    args      : Vars.var list;
    indices   : Vars.var list;
    path_cond : PathCond.t;
  }

  let mk ~env ~msymb ~args ~indices ~path_cond : t =
    let indices = Sv.diff (Sv.of_list1 indices) env in
    let indices = Sv.elements indices in
    { msymb; args; indices; path_cond; }

  let pp fmt (mset : t) =
    Fmt.pf fmt "@[<hv 2>{ @[%a@]@@_ |@ %a%a}@]"
      Term.pp_msymb mset.msymb
      (Fmt.list ~sep:Fmt.comma Vars.pp) mset.indices 
      PathCond.pp mset.path_cond

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
              else true, Vars.make_fresh Type.Index "i"

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
    let join_ms = Term.mk_symb a_ms.s_symb a_ms.s_typ in

    let path_cond = PathCond.join a.path_cond b.path_cond in
    mk ~env:Sv.empty ~msymb:join_ms ~args:join_is ~path_cond ~indices:(!indices_r)

  let incl table (sexpr : SE.fset) (s1 : t) (s2 : t) : bool =
    let tv = Vars.make_fresh Type.Timestamp "t" in
    let term1 = Term.mk_macro s1.msymb (Term.mk_vars s1.args) (Term.mk_var tv) in
    let term2 = Term.mk_macro s2.msymb (Term.mk_vars s2.args) (Term.mk_var tv) in

    let pat2 = Term.{ 
        pat_term   = term2;
        pat_tyvars = [];
        pat_vars   = Sv.of_list1 s2.indices;}
    in
    let system = SE.reachability_context sexpr in
    match Match.T.try_match table system term1 pat2 with
    | Match _ -> true
    | FreeTyv | NoMatch _ -> false

  let mk_simple (m : Symbols.macro) ty : t =
    let msymb = Term.mk_symb m ty in
    mk ~env:Sv.empty ~msymb ~args:[] ~indices:[] ~path_cond:Top
end

module MsetAbs : sig[@warning "-32"]
  (** Abstract value containing one mset per macro symbol. *)
  type t = (Symbols.macro * Mset.t) list

  val pp : Format.formatter -> t -> unit

  (** Join a single [mset] into an full abstract value. *)
  val join_single : Mset.t -> t -> t

  (** Join operator. *)
  val join : t -> t -> t

  (** [incl ... abs1 abs2] checks if [abs1 ⊆ abs2]. *)
  val incl : Symbols.table -> SE.fset -> t -> t -> bool

  (** [diff ... abs1 abs2] over-approximates [abs1 \ abs2]. *)
  val diff : Symbols.table -> SE.fset -> t -> t -> t
end = struct
  type t = (Symbols.macro * Mset.t) list

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
end

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
  Mset.mk ~env ~msymb:occ.occ_cnt.symb ~args:indices ~indices ~path_cond

(*------------------------------------------------------------------*)
(** Return an over-approximation of the macros reachable from a term
    in any trace model. *)
let macro_support
    ~(env  : Sv.t) 
    (cntxt : Constr.trace_cntxt)
    (term  : Term.term)
  : MsetAbs.t
  =
  let get_msymbs
      ~(mode : [`Delta | `FullDelta ]) 
      ~(path_cond : PathCond.t)
      (term  : Term.term) 
    : MsetAbs.t 
    =
    let occs = get_macro_occs ~mode cntxt term in
    let msets = List.map (mset_of_macro_occ env ~path_cond) occs in
    List.fold_left (fun abs mset -> MsetAbs.join_single mset abs) [] msets
  in

  let init : MsetAbs.t = get_msymbs ~mode:`FullDelta ~path_cond:Top term in

  (* all actions names of the system *)
  let all_actions : Symbols.action list = 
    SE.fold_descrs (fun d l -> d.name :: l) cntxt.table cntxt.system []
  in

  let do1 (sm : MsetAbs.t) : MsetAbs.t =
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

    SE.fold_descrs (fun (descr : Action.descr) (sm : MsetAbs.t) ->
        fold_descr ~globals:true
          (fun
            (msymb : Symbols.macro) 
            (_ : Vars.vars) (m_is : Vars.vars) 
            _ (t : Term.term) (sm : MsetAbs.t) ->
             if List.mem_assoc msymb sm then
               (* we compute the substitution which we will use to instantiate
                  [t] on the indices of the macro set in [sm]. *)
               let subst =
                 let mset = List.assoc msymb sm in
                 List.map2 (fun i j ->
                     Term.ESubst (Term.mk_var i, Term.mk_var j)
                   ) m_is mset.Mset.args
               in
               let t = Term.subst subst t in

               (* compute a valid path condition *)
               let path_cond =
                 PathCond.concat ~all_actions
                   (PathCond.Before [descr]) (List.assoc msymb sm).path_cond 
               in

               MsetAbs.join (get_msymbs ~mode:`Delta ~path_cond t) sm
                 
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


(*------------------------------------------------------------------*)
(** See `.mli` *)
type iocc = {
  iocc_aname     : Symbols.action;
  iocc_action    : Action.action;
  iocc_vars      : Sv.t;
  iocc_cnt       : Term.term;
  iocc_sources   : Term.term list;

  iocc_path_cond : PathCond.t;
}

let pp_iocc fmt (o : iocc) : unit =
  Fmt.pf fmt "@[<v 2>[%a(%a):@;cnt: @[%a@]@;sources: @[%a@]@;fv: @[%a@]]@]"
    Symbols.pp o.iocc_aname
    (Fmt.list ~sep:Fmt.comma Term.pp) (Action.get_args o.iocc_action)
    Term.pp o.iocc_cnt
    (Fmt.list ~sep:Fmt.comma Term.pp) o.iocc_sources
    (Fmt.list ~sep:Fmt.comma Vars.pp) (Sv.elements o.iocc_vars)

(** Folding over all macro descriptions reachable from some terms.
    [env] must contain the free variables of [terms]. 
    See the function [fold_macro_support] below for a more detailed 
    description. *)
let _fold_macro_support
    (func  : ((unit -> Action.descr) -> iocc -> 'a -> 'a))
    (cntxt : Constr.trace_cntxt)
    (env   : Vars.env)
    (terms : Term.term list)
    (init  : 'a) : 'a
  =
  let env = Vars.to_set env in

  (* association list of terms and their macro support *)
  let sm : (Term.term * MsetAbs.t) list =
    List.map (fun src -> (src, macro_support ~env cntxt src)) terms
  in

  if pp_dbg then                (* debug printing, turned-off  *)
    List.iter (fun (_, mset_abs) -> Fmt.epr "macro_support:@.%a@." MsetAbs.pp mset_abs ) sm;

  (* reversing the association map: we want to map macros to
     pairs of possible sources and macro set *)
  let macro_occs : (Term.term list * Mset.t) Ms.t =
    List.fold_left (fun macro_occs ((src, src_macros) : Term.term * MsetAbs.t) ->
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

  SE.fold_descrs (fun descr acc ->
      fold_descr ~globals:true (fun msymb _ m_is _ t acc ->
          if Ms.mem msymb macro_occs then
            let srcs, mset = Ms.find msymb macro_occs in

            let m_is' = mset.Mset.args in
            (* we compute the substitution which we will use to instantiate
               [t] on the indices of the macro set in [mset]. *)
            let subst =
              List.map2 (fun i j ->
                  Term.ESubst (Term.mk_var i, Term.mk_var j)
                ) m_is m_is'
            in

            let iocc_cnt = Term.subst subst t in
            let iocc_action = 
              Action.subst_action subst (Action.to_action descr.action) 
            in
            let iocc_fv = 
              Sv.union (Action.fv_action iocc_action) (Term.fv iocc_cnt) 
            in
            let iocc = {
              iocc_aname   = descr.name;
              iocc_vars    = Sv.diff iocc_fv env;
              iocc_action;
              iocc_cnt;
              iocc_sources = srcs;
              iocc_path_cond = mset.path_cond;
            } in

            let descr () = Action.subst_descr subst descr in

            func descr iocc acc
          else acc
        ) cntxt.table cntxt.system descr acc
    ) cntxt.table cntxt.system init

(** See `.mli` for a complete description *)
let fold_macro_support
    (func  : (iocc -> 'a -> 'a))
    (cntxt : Constr.trace_cntxt)
    (env   : Vars.env)
    (terms : Term.term list)
    (init  : 'a) : 'a
  =
  _fold_macro_support (fun _ -> func) cntxt env terms init

(** Less precise version of [fold_macro_support], which does not track 
    sources. *)
let fold_macro_support0
    (func : (
        Symbols.action -> (* action name *)
        Action.action ->  (* action *)
        Term.term ->      (* term *)
        'a -> 'a))
    (cntxt : Constr.trace_cntxt)
    (env   : Vars.env)
    (terms : Term.term list)
    (init  : 'a) : 'a
  =
  _fold_macro_support (fun _ iocc acc ->
      func iocc.iocc_aname iocc.iocc_action iocc.iocc_cnt acc
    ) cntxt env terms init


(** Less precise version of [fold_macro_support], which does not track 
    sources. *)
let fold_macro_support1
    (func  : (Action.descr -> Term.term -> 'a -> 'a))
    (cntxt : Constr.trace_cntxt)
    (env   : Vars.env)
    (terms : Term.term list)
    (init  : 'a) : 'a
  =
  _fold_macro_support (fun descr iocc acc ->
      func (descr ()) iocc.iocc_cnt acc
    ) cntxt env terms init
