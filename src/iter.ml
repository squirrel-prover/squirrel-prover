open Term

(*------------------------------------------------------------------*)
let refresh vars =
  List.map (fun v ->
      ESubst (Var v, Var (Vars.make_new_from v))
    ) vars

let erefresh evars =
  List.map (function Vars.EVar v ->
      ESubst (Var v, Var (Vars.make_new_from v))
    ) evars

(*------------------------------------------------------------------*)
(** Iterate over all boolean and message subterms.
  * Bound variables are represented as newly generated fresh variables.
  * When a macro is encountered, its expansion is visited as well. *)
class iter ~(cntxt:Constr.trace_cntxt) = object (self)

  method visit_term t = match t with
    | Equiv.Message e -> self#visit_message e
    | Equiv.Formula e -> self#visit_formula e

  method visit_message t = match t with
    | Fun (_, l) -> List.iter self#visit_message l
    | Macro ((mn,sort,is),l,a) ->
        if l<>[] then failwith "Not implemented" ;
        self#visit_message (Macros.get_definition cntxt sort mn is a)
    | Name _ | Var _ -> ()
    | Diff(a, b) -> self#visit_message a; self#visit_message b
    | ITE (a, b, c) ->
        self#visit_formula a; self#visit_message b; self#visit_message c
    | Seq (a, b) ->
        let b = Term.subst (refresh a) b in
        self#visit_message b
    | Find (a, b, c, d) ->
        let subst = refresh a in
        let b = Term.subst subst b in
        let c = Term.subst subst c in
        self#visit_formula b; self#visit_message c; self#visit_message d

  method visit_formula (f:Term.formula) =
    match f with
    | And (l,r) | Or (l,r) | Impl (l,r) ->
        self#visit_formula l ;
        self#visit_formula r
    | Not f -> self#visit_formula f
    | True | False -> ()
    | Diff(a, b) -> self#visit_formula a; self#visit_formula b
    | ForAll (vs,l) | Exists (vs,l) ->
        let subst = erefresh vs in
        let l = Term.subst subst l in
        self#visit_formula l
    | Atom (`Message (_, t, t')) ->
        self#visit_message t ;
        self#visit_message t'
    | Atom (`Index _) | Atom (`Timestamp _) | Atom (`Happens _) -> ()
    | Macro ((mn,Sorts.Boolean,is),l,a) ->
        if l<>[] then failwith "Not implemented" ;
        self#visit_formula
          (Macros.get_definition cntxt Sorts.Boolean mn is a)
    | Var _ -> ()

end

(** Fold over all boolean and message subterms.
  * Bound variables are represented as newly generated fresh variables.
  * When a macro is encountered, its expansion is visited as well.
  * Note that [iter] could be obtained as a derived class of [fold],
  * but this would break the way we modify the iteration using inheritance.  *)
class ['a] fold ~(cntxt:Constr.trace_cntxt) = object (self)

  method fold_term (x:'a) t = match t with
    | Equiv.Message e -> self#fold_message x e
    | Equiv.Formula e -> self#fold_formula x e

  method fold_message x t = match t with
    | Fun (_, l) -> List.fold_left self#fold_message x l
    | Macro ((mn,sort,is),l,a) ->
        if l<>[] then failwith "Not implemented" ;
        self#fold_message x (Macros.get_definition cntxt sort mn is a)
    | Name _ | Var _ -> x
    | Diff (a, b) -> self#fold_message (self#fold_message x a) b
    | ITE (a, b, c) ->
        self#fold_message (self#fold_message (self#fold_formula x a) b) c
    | Seq (a, b) ->
        let b = Term.subst (refresh a) b in
        self#fold_message x b
    | Find (a, b, c, d) ->
        let subst = refresh a in
        let b = Term.subst subst b in
        let c = Term.subst subst c in
        let d = Term.subst subst d in
        self#fold_message (self#fold_message (self#fold_formula x b) c) d

  method fold_formula x f =
    match f with
    | And (l,r) | Or (l,r) | Impl (l,r) ->
        self#fold_formula (self#fold_formula x l) r
    | Not f -> self#fold_formula x f
    | True | False -> x
    | Diff(a, b) -> self#fold_formula (self#fold_formula x a) b
    | ForAll (vs,l) | Exists (vs,l) ->
        let subst = erefresh vs in
        let l = Term.subst subst l in
        self#fold_formula x l
    | Atom (`Message (_, t, t')) ->
        self#fold_message (self#fold_message x t) t'
    | Atom (`Index _) | Atom (`Timestamp _) | Atom (`Happens _) -> x
    | Macro ((mn,Sorts.Boolean,is),l,a) ->
        if l<>[] then failwith "Not implemented" ;
        self#fold_formula x
          (Macros.get_definition cntxt Sorts.Boolean mn is a)
    | Var _ -> x

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
class iter_approx_macros ~exact ~full ~(cntxt:Constr.trace_cntxt) = object (self)

  inherit iter ~cntxt as super

  val mutable checked_macros = []

  method visit_macro mn is a =
    match Symbols.Macro.get_def mn cntxt.table with
      | Symbols.(Input | Output | State _ | Cond | Exec | Frame) -> ()
      | Symbols.Global _ ->
          if exact then
            if full || Macros.is_defined mn a cntxt.table then
              self#visit_message
                (Macros.get_definition cntxt Sorts.Message mn is a)
            else ()
          else if not (List.mem mn checked_macros) then begin
            checked_macros <- mn :: checked_macros ;
            self#visit_message
              (Macros.get_dummy_definition cntxt Sorts.Message mn is)
          end
      | Symbols.Local _ -> assert false (* TODO *)

  method visit_message = function
    | Macro ((mn,sort,is),[],a) -> self#visit_macro mn is a
    | m -> super#visit_message m

  method visit_formula = function
    | Macro ((mn,sort,is),[],a) -> self#visit_macro mn is a
    | f -> super#visit_formula f

  method has_visited_macro mn = List.mem mn checked_macros

end

(** Collect occurrences of [f(_,k(_))] or [f(_,_,k(_))] for a function name [f]
   and name [k]. We use the exact version of [iter_approx_macros], otherwise we
   might obtain meaningless terms provided by [get_dummy_definition]. *)
class get_f_messages ?(drop_head=true) ~(cntxt:Constr.trace_cntxt) f k = object (self)
  inherit iter_approx_macros ~exact:true ~full:true ~cntxt as super
  val mutable occurrences : (Vars.index list * Term.message) list = []
  method get_occurrences = occurrences
  method visit_message = function
    | Term.Fun ((f',_), [m;k']) as m_full when f' = f ->
        begin match k' with
          | Term.Name (k',is) when k' = k ->
              let ret_m = if drop_head then m else m_full in
              occurrences <- (is,ret_m) :: occurrences
          | _ -> ()
        end ;
        self#visit_message m ; self#visit_message k'
    | Term.Fun ((f',_), [m;r;k']) as m_full when f' = f ->
        begin match k' with
          | Term.Name (k',is) when k' = k ->
              let ret_m = if drop_head then m else m_full in
              occurrences <- (is,ret_m) :: occurrences
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
  inherit iter_approx_macros ~exact:true ~full:true ~cntxt as super
  val mutable func : Term.message list = []
  method get_func = func
  method visit_message = function
    | Term.Fun ((fn,_), l) as fn_term ->
        if Symbols.is_ftype fn symtype cntxt.table
        then func <-  fn_term :: func
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
  List.iter iter#visit_term [elem];
  match iter#get_func with
  | p::q -> Some p
  | [] -> None

let get_ftypes ?excludesymtype ~(cntxt:Constr.trace_cntxt) elem stype =
  let iter = new get_ftypes_term ?excludesymtype ~cntxt stype in
  List.iter iter#visit_term [elem];
  iter#get_func



(** {2 If-Then-Else} *)
class get_ite_term ~(cntxt:Constr.trace_cntxt) = object (self)
  inherit iter_approx_macros ~exact:true ~full:false ~cntxt as super
  val mutable ite : (Term.formula * Term.message * Term.message) option = None
  method get_ite = ite
  method visit_message = function
    | Term.ITE (c,t,e) ->
        ite <- Some (c,t,e)
    | m -> super#visit_message m
end
