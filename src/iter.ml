open Term

(** Iterate on all subfacts and subterms.
  * When a macro is encountered, its expansion is visited as well. *)
class iter = object (self)

  method visit_term t = match t with
    | Fun (_, l) -> List.iter self#visit_term l
    | Macro ((mn, is),l,a) ->
        List.iter self#visit_term l ;
        self#visit_term (Macros.get_definition mn is a)
    | Name _ | Var _ -> ()

  method visit_formula (f:Formula.formula) =
    let open Formula in
    match f with
    | And (l,r) | Or (l,r) | Impl (l,r) ->
        self#visit_formula l ;
        self#visit_formula r
    | Not f -> self#visit_formula f
    | True | False -> ()
    | ForAll (vs,l) | Exists (vs,l) -> self#visit_formula l
    | Atom (`Message (_, t, t')) ->
        self#visit_term t ;
        self#visit_term t'
    | _ -> ()
end

(** Iterator that does not visit macro expansions but guarantees
  * that whenever a macro [m(...)@..] occurs where [m] is not an input/output,
  * a specific expansion of [m] will have been visited, without
  * any guarantee on the indices and action used for that expansion. *)
class iter_approx_macros = object (self)

  inherit iter as super

  val mutable checked_macros = [fst Term.in_macro;fst Term.out_macro]

  method visit_term t = match t with
    | Macro ((mn,is),l,_) ->
        List.iter self#visit_term l ;
        if not (List.mem mn checked_macros) then begin
          checked_macros <- mn :: checked_macros ;
          self#visit_term (Macros.get_dummy_definition mn is)
        end
    | _ -> super#visit_term t

end
