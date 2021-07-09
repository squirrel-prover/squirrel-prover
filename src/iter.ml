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
      let t = match Macros.get_definition cntxt ms a with
        | `Undef | `MaybeDef -> assert false (* must be defined *)
        | `Def t -> t
      in
      self#visit_message t
        
    | Name _ | Var _ -> ()

    | Diff(a, b) -> self#visit_message a; self#visit_message b

    | Seq (a, b) ->
      let _, s = Term.refresh_vars `Global a in
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
      let _, s = Term.refresh_vars `Global a in
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
          | `Undef | `MaybeDef -> () (* TODO: shouldn't this be assert false ? *)
                                  
        else if not (List.mem ms.s_symb checked_macros) then begin
          checked_macros <- ms.s_symb :: checked_macros ;
          self#visit_message
            (Macros.get_dummy_definition cntxt ms)
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
  Fmt.pf fmt "[%a | ∃%a, %a]" 
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
    let is, subst = Term.refresh_vars `Global is in
    let t = Term.subst subst t in
    let fv = Sv.add_list fv is in
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
    func ~fv:fv  ~cond:(Term.mk_and cond (Term.mk_not c)) (Term.ETerm e)  

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

(** Looks for occurrences of subterms using a function symbol of the given kind 
    (Hash, Dec, ...).
    Does not recurse below terms whose head is excluded by [excludesymtype]. *)
let get_ftypes : type a.
  ?excludesymtype:Symbols.function_def ->
  Symbols.table ->
  Symbols.function_def ->
  a Term.term -> mess_occs = 
  fun ?excludesymtype table symtype t ->
  
    let rec get : 
    type a. a Term.term -> fv:Sv.t -> cond:Term.message -> mess_occs =
    fun t ~fv ~cond ->
      let occs () =       
        tfold_occ ~mode:`NoDelta (fun ~fv ~cond (Term.ETerm t) occs -> 
            get t ~fv ~cond @ occs
          ) ~fv ~cond t []
      in

      match t with
      | Term.Fun ((fn,_),_,l) ->
        let head_occ = 
          if Symbols.is_ftype fn symtype table
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
        
      | _ -> occs ()
  in
  
  get t ~fv:Sv.empty ~cond:Term.mk_true

(*------------------------------------------------------------------*)
(** {2 Find [h(_, k)]} *)

(* pair of the key indices and the term *)
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

(** Looks for macro occurrences in a term.
    Macros that can be expanded are ignored.
    Raise @Var_found if a term variable occurs in the term. *)
let get_macro_occs : type a. 
  mode:[`Delta of Constr.trace_cntxt | `NoDelta ] ->
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
        let occ = { 
            occ_cnt  = ms;
            occ_vars = fv; 
            occ_cond = cond; } 
        in
        [occ]

      | _ -> 
        tfold_occ ~mode
          (fun ~fv ~cond (Term.ETerm t) occs -> 
             get t ~fv ~cond @ occs
          ) ~fv ~cond t []
  in
  get t ~fv:Sv.empty ~cond:Term.mk_true

(*------------------------------------------------------------------*)
module Sm = Symbols.Ss(Symbols.Macro)

(** Return the macro symbols reachable from a term in any trace model. *)
let macro_support : type a. 
  Constr.trace_cntxt -> 
  a Term.term list -> 
  Sm.t
  = 
  fun cntxt terms ->
  let get_msymbs : type a.
    mode:[`Delta of Constr.trace_cntxt | `NoDelta ] -> 
    a Term.term -> 
    Sm.t 
    = 
    fun ~mode term ->
    let occs = get_macro_occs ~mode cntxt term in
    let msymbs = List.map (fun occ -> occ.occ_cnt.Term.s_symb) occs in
    Sm.of_list msymbs
  in

  let init = List.fold_left (fun init term ->
      Sm.union (get_msymbs ~mode:(`Delta cntxt) term) init
    ) Sm.empty terms
  in

  let do1 (sm : Sm.t) = 
    (* special cases for Input, Frame and Exec, since they do not appear in the 
       action descriptions. *)
    let sm = if Sm.mem Symbols.inp sm then Sm.add Symbols.frame sm else sm in
    let sm = 
      if Sm.mem Symbols.frame sm 
      then Sm.add Symbols.exec (Sm.add Symbols.out sm)
      else sm 
    in
    let sm = 
      if Sm.mem Symbols.exec sm 
      then Sm.add Symbols.cond (Sm.add Symbols.out sm) 
      else sm 
    in

    SystemExpr.fold_descrs (fun descr sm ->
        Action.fold_descr (fun msymb _ t sm ->
            if Sm.mem msymb sm 
            then Sm.union (get_msymbs ~mode:`NoDelta t) sm 
            else sm
          ) descr sm
      ) cntxt.table cntxt.system sm
  in

  Utils.fpt Sm.equal do1 init 


(** Folding over all macro descriptions reachable from some terms. *)    
let fold_macro_support : type a. 
  (Action.descr -> Term.message -> 'b -> 'b) ->
  Constr.trace_cntxt -> 
  a Term.term list -> 
  'b ->
  'b
  = 
  fun func cntxt terms init ->
  let sm = macro_support cntxt terms in
  SystemExpr.fold_descrs (fun descr acc ->
      Action.fold_descr (fun msymb _ t acc ->
          if Sm.mem msymb sm then func descr t acc else acc
        ) descr acc
    ) cntxt.table cntxt.system init
