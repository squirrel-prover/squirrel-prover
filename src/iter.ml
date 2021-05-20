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
        self#visit_message (Macros.get_definition cntxt ms a)

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
        self#fold_message x (Macros.get_definition cntxt ms a)

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
            if Macros.is_defined ms.s_symb a cntxt.table then
              self#visit_message
                (Macros.get_definition cntxt ms a)
            else ()

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

(** Get the terms of given type, that do not appear under a symbol of the
   excluded type. *)
class get_ftypes_term
    ?excludesymtype ~(cntxt:Constr.trace_cntxt) symtype = object (self)
  inherit iter_approx_macros ~exact:true ~cntxt as super
  val mutable func : Term.message list = []
  method get_func = func
  method visit_message = function
    | Term.Fun ((fn,_),_,l) as fn_term ->
        if Symbols.is_ftype fn symtype cntxt.table
        then func <- fn_term :: func
        else begin
          match excludesymtype with
          | Some ex when Symbols.is_ftype fn ex cntxt.table -> ()
          | _ -> List.iter self#visit_message l
        end
    | m -> super#visit_message m
end

(** [get_ftype ~system elem ftype] returns [None] if there is no term in [elem]
   with a function symbol head of the fiven ftype, [Some fun] otherwise, where
   [fun] is the first term of the given type encountered. Does not explore
   macros. *)
let get_ftype ~(cntxt:Constr.trace_cntxt) elem stype =
  let iter = new get_ftypes_term ~cntxt stype in
  List.iter iter#visit_message [elem];
  match iter#get_func with
  | p::q -> Some p
  | [] -> None

let get_ftypes ?excludesymtype ~(cntxt:Constr.trace_cntxt) elem stype =
  let iter = new get_ftypes_term ?excludesymtype ~cntxt stype in
  List.iter iter#visit_message [elem];
  iter#get_func

(*------------------------------------------------------------------*)
(** {2 Occurrences} *)
type 'a occ = { 
  occ_cnt  : 'a;              
  occ_vars : Sv.t;             (* variables binded above the occurrence *)
  occ_cond : Term.message;     (* conditions above the occurrence *)
}

type 'a occs = 'a occ list  

(** Like [Term.tfold], but also propagate downward (globally refreshed) 
    binded variables and conditions. *)
let tfold_occ : type b.
  (fv:Sv.t -> cond:Term.message -> Term.eterm -> 'a -> 'a) -> 
  fv:Sv.t -> cond:Term.message -> b Term.term -> 'a -> 'a = 
  fun func ~fv ~cond t acc ->
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

  | Term.Macro  _
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
        tfold_occ (fun ~fv ~cond (Term.ETerm t) occs -> 
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
    
