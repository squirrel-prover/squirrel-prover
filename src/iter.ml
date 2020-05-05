open Term

(** Iterate on all subfacts and subterms.
  * Bound variables are represented as newly generated fresh variables.
  * When a macro is encountered, its expansion is visited as well. *)
class iter ~system = object (self)

  method visit_term t = match t with
    | EquivSequent.Message e -> self#visit_message e
    | EquivSequent.Formula e -> self#visit_formula e

  method visit_message t = match t with
    | Fun (_, l) -> List.iter self#visit_message l
    | Macro ((mn, sort, is),l,a) ->
        List.iter self#visit_message l ;
        self#visit_message (Macros.get_definition system sort mn is a)
    | Name _ | Var _ -> ()
    | Diff(a, b) -> self#visit_message a; self#visit_message b
    | ITE (a, b, c) ->
        self#visit_formula a; self#visit_message b; self#visit_message c
    | Seq (a, b) ->
        let subst =
          List.map
            (fun v -> ESubst (Var v,
                              Var (Vars.make_new_from v)))
            a
        in
        let b = Term.subst subst b in
        self#visit_message b
    | Find (a, b, c, d) ->
        let subst =
          List.map
            (fun v -> ESubst (Var v,
                              Var (Vars.make_new_from v)))
            a
        in
        let b = Term.subst subst b in
        let c = Term.subst subst c in
        let d = Term.subst subst d in
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
        let subst =
          List.map
            (function
               | Vars.EVar v ->
                   ESubst (Var v, Var (Vars.make_new_from v)))
            vs
        in
        let l = Term.subst subst l in
        self#visit_formula l
    | Atom (`Message (_, t, t')) ->
        self#visit_message t ;
        self#visit_message t'
    | Atom (`Index _) | Atom (`Timestamp _)-> ()
    | Macro ((mn, Sorts.Boolean, is),[],a) ->
        self#visit_formula
          (Macros.get_definition system Sorts.Boolean mn is a)
    | _ -> failwith "unsupported"

end

(** Iterator that does not visit macro expansions but guarantees that,
  * for macro symbols [m] other that input, output, cond, exec, frame
  * and states, if [m(...)@..] occurs in the visited terms then
  * a specific expansion of [m] will have been visited, without
  * any guarantee on the indices and action used for that expansion,
  * because [get_dummy_definition] is used -- this behaviour is disabled
  * with [exact], in which case all macros will be expanded and must
  * thus be defined. *)
class iter_approx_macros ~exact ~system = object (self)

  inherit iter ~system as super

  val mutable checked_macros = []

  method visit_macro mn is a =
    match Symbols.Macro.get_def mn with
      | Symbols.(Input | Output | State _ | Cond | Exec | Frame) -> ()
      | Symbols.Global _ ->
          if exact then
            self#visit_message
              (Macros.get_definition system Sorts.Message mn is a)
          else if not (List.mem mn checked_macros) then begin
            checked_macros <- mn :: checked_macros ;
            self#visit_message
              (Macros.get_dummy_definition system Sorts.Message mn is)
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

(** Collect occurrences of [f(_,k(_))] for a function symbol [f] and name [k].
  * We use the exact version of [iter_approx_macros], otherwise
  * we might obtain meaningless terms provided by [get_dummy_definition]. *)
class get_f_messages ~system f k = object (self)
  inherit iter_approx_macros ~exact:true ~system as super
  val mutable occurrences : (Vars.index list * Term.message) list = []
  method get_occurrences = occurrences
  method visit_message = function
    | Term.Fun ((f',_), [m;k']) when f' = f ->
        begin match k' with
          | Term.Name (k',is) when k' = k ->
              occurrences <- (is,m) :: occurrences
          | _ -> ()
        end ;
        self#visit_message m ; self#visit_message k'
    | Term.Var m -> assert false (* SSC must have been checked first *)
    | m -> super#visit_message m
end

(** Get the terms of given type. *)
class get_ftypes_term ~system symtype = object (self)
  inherit iter_approx_macros ~exact:true ~system as super
  val mutable func : Term.message list = []
  method get_func = func
  method visit_message = function
    | Term.Fun ((fn,_), l) as fn_term ->
        if  Symbols.is_ftype fn symtype
        then func <-  fn_term :: func
        else List.iter self#visit_message l
    | m -> super#visit_message m
end

(** [get_ftype ~system elem ftype] returns None if there is no term in [elem]
   with a function symbol head of the fiven ftype, Some fun otherwise, where
   [fun] is the first term of the given type encountered. Does not explore
   macros. *)
let get_ftype ~system elem stype =
  let iter = new get_ftypes_term ~system stype in
  List.iter iter#visit_term [elem];
  match iter#get_func with
  | p::q -> Some p
  | [] -> None

let get_ftypes ~system elem stype =
  let iter = new get_ftypes_term ~system stype in
  List.iter iter#visit_term [elem];
  iter#get_func
