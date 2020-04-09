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
