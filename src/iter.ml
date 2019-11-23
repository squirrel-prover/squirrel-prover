open Term
open Bformula

class iter = object (self)

  method visit_term t = match t with
    | Fun (_, l) -> List.iter self#visit_term l
    | Macro ((mn, is), a) ->
        begin match a with
          | Term.TName a when List.length a = Term.macro_domain mn ->
              self#visit_term (Term.macro_declaration mn a is)
          | _ -> failwith "cannot visit opaque macro"
        end
    | State _ -> failwith "visiting state not implemented"
    | Name _ | MVar _ -> ()

  method visit_fact (f:fact) = match f with
    | And (l,r) | Or (l,r) | Impl (l,r) ->
        self#visit_fact l ;
        self#visit_fact r
    | Not f -> self#visit_fact f
    | True | False -> ()
    | Atom (_, t, t') ->
        self#visit_term t ;
        self#visit_term t'

end

(** Iterator that does not visit macro expansions but guarantees
  * that whenever a macro [m(...)@..] occurs where [m] is not builtin,
  * a specific expansion of [m] will have been visited, without
  * any guarantee on the indices and action used for that expansion. *)
class iter_approx_macros = object (self)

  inherit iter as super

  val mutable checked_macros = []

  method visit_term t = match t with
    | Macro ((mn,is),_) ->
        if List.mem mn checked_macros || Term.is_built_in mn then ()
        else begin
          checked_macros <- mn :: checked_macros ;
          let rec dummy_action k =
            if k = 0 then [] else
              { Action.par_choice = 0,[] ; sum_choice = 0,[] }
              :: dummy_action (k-1)
          in
          let dummy_action = dummy_action (Term.macro_domain mn) in
            self#visit_term (Term.macro_declaration mn dummy_action is)
        end
    | _ -> super#visit_term t

end
