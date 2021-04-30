
exception Name_found
exception Var_found
exception Not_name

class find_name ~(cntxt:Constr.trace_cntxt) exact name = object (self)
  inherit Iter.iter_approx_macros ~exact ~full:true ~cntxt as super

  method visit_message t = match t with
    | Term.Name ns -> if ns.s_symb = name then raise Name_found
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

class get_name_indices ~(cntxt:Constr.trace_cntxt) exact name = object (self)
  inherit Iter.iter_approx_macros ~exact ~full:true ~cntxt as super

  val mutable indices : (Vars.index list) list = []
  method get_indices = List.sort_uniq Stdlib.compare indices

  method visit_message t = match t with
    | Term.Name ns -> 
      if ns.s_symb = name then indices <- ns.s_indices :: indices

    | Term.Var m -> raise Var_found

    | _ -> super#visit_message t
end

class get_actions ~(cntxt:Constr.trace_cntxt) = object (self)
  inherit Iter.iter_approx_macros ~exact:false ~full:true ~cntxt as super

  (* The boolean is set to true only for input macros.
   * In that case, when building phi_proj we require a strict inequality on
   * timestamps because we have to consider only actions occurring before
   * the input.*)
  val mutable actions : (Term.timestamp * bool) list = []
  method get_actions = List.sort_uniq Stdlib.compare actions

  method visit_macro mn a = 
    match Symbols.Macro.get_def mn.s_symb cntxt.table with
    | Symbols.Input -> actions <- (a,true)  :: actions
    | _             -> actions <- (a,false) :: actions
end
