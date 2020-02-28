open Term

(** Iterate on all subfacts and subterms.
  * When a macro is encountered, its expansion is visited as well. *)
class iter ~system_id = object (self)

  method visit_message t = match t with
    | Fun (_, l) -> List.iter self#visit_message l
    | Macro ((mn, sort, is),l,a) ->
        List.iter self#visit_message l ;
        self#visit_message (Macros.get_definition ~system_id sort mn is a)
    | Name _ | Var _ -> ()
    | Diff(a, b) -> self#visit_message a; self#visit_message b
    | Left a -> self#visit_message a
    | Right a -> self#visit_message a
    | ITE (a, b, c) -> self#visit_formula a;
      self#visit_message b; self#visit_message c
    | Find (a, b, c, d) ->
        self#visit_formula b; self#visit_message c; self#visit_message d

  method visit_formula (f:Term.formula) =
    match f with
    | And (l,r) | Or (l,r) | Impl (l,r) ->
        self#visit_formula l ;
        self#visit_formula r
    | Not f -> self#visit_formula f
    | True | False -> ()
    | ForAll (vs,l) | Exists (vs,l) -> self#visit_formula l
    | Atom (`Message (_, t, t')) ->
        self#visit_message t ;
        self#visit_message t'
    | Macro ((mn, Sorts.Boolean, is),[],a) ->
      (* TODO : if we visit the subterm here, we have a recursive infinite loop
         due to exec. *)
      ()
    | _ -> failwith "unsupported"

end

(** Iterator that does not visit macro expansions but guarantees that,
  * for macro symbols [m] other that input, output and states,
  * if [m(...)@..] occurs in the visited terms then
  * a specific expansion of [m] will have been visited, without
  * any guarantee on the indices and action used for that expansion. *)
class iter_approx_macros ~system_id = object (self)

  inherit iter ~system_id as super

  val mutable checked_macros = []

  method visit_message (t : Term.message) = match t with
    | Macro ((mn,sort,is),l,_) ->
        begin match Symbols.Macro.get_def mn with
          | Symbols.(Input | Output | State _) -> ()
          | Symbols.Global _ ->
              List.iter self#visit_message l ;
              if not (List.mem mn checked_macros) then begin
                checked_macros <- mn :: checked_macros ;
                self#visit_message
                  (Macros.get_dummy_definition ~system_id sort mn is)
              end
          | Symbols.(Frame | Local _) -> assert false (* TODO *)
          | Symbols.(Cond | Exec) ->
              (* These symbols do not make sense in messages.
               * TODO they could be ruled out using stronger typing. *)
              assert false
        end
    | _ -> super#visit_message t

end
