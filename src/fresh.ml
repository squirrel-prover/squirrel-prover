
exception Name_found
exception Var_found
exception Not_name

class find_name ~(system:SystemExpr.system_expr) table exact name = object (self)
  inherit Iter.iter_approx_macros ~exact ~system table as super

  method visit_message t = match t with
    | Term.Name (n,_) -> if n = name then raise Name_found
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

class get_name_indices ~(system:SystemExpr.system_expr) table exact name = object (self)
  inherit Iter.iter_approx_macros ~exact ~system table as super

  val mutable indices : (Vars.index list) list = []
  method get_indices = List.sort_uniq Stdlib.compare indices

  method visit_message t = match t with
    | Term.Name (n,is) -> if n = name then indices <- is::indices
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

class get_actions ~(system:SystemExpr.system_expr) table exact = object (self)
  inherit Iter.iter_approx_macros ~exact ~system table as super

  (* The boolean is set to true only for input macros.
   * In that case, when building phi_proj we require a strict inequality on
   * timestamps because we have to consider only actions occurring before
   * the input.*)
  val mutable actions : (Term.timestamp * bool) list = []
  method get_actions = List.sort_uniq Stdlib.compare actions

  method visit_macro mn is a = match Symbols.Macro.get_def mn table with
    | Symbols.Input -> actions <- (a,true)::actions
    | Symbols.(Output | State _ | Cond | Exec | Frame) ->
      actions <- (a,false)::actions
    | _ -> (actions <- (a, false)::actions; self#visit_macro mn is a)
end
