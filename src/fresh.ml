module Sv = Vars.Sv

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

  val mutable actions : Term.timestamp list = []
  method get_actions = actions

  method visit_macro mn a =     
    let cleara, a' = match Symbols.Macro.get_def mn.s_symb cntxt.table with
      | Symbols.Input -> true,  Term.Pred a
      | _             -> false, a
    in
    if not (List.mem a' actions) then
      actions <- a' :: actions;
    
    (* remove [(a,false)] if it appeared in [actions] *)
    if cleara then 
      actions <- List.filter (fun a0 -> a0 <> a) actions
 end


(*------------------------------------------------------------------*)
type macro_ts_occ = { 
  mtso_ts   : Term.timestamp;
  mtso_vars : Sv.t;
  mtso_cond : Term.message;
}

type macro_ts_occs = macro_ts_occ list  

(** remove duplicates from occs for some subsuming relation. *)
let clear_dup_mtso_le occs = 
  let subsumes occ1 occ2 =
    (* TODO: alpha-renaming *)
    Sv.equal occ1.mtso_vars occ2.mtso_vars &&
    occ1.mtso_cond = occ2.mtso_cond &&
    (occ1.mtso_ts = occ2.mtso_ts || occ1.mtso_ts = Term.Pred occ2.mtso_ts)
  in
  let occs = 
    List.fold_left (fun acc occ -> 
        let acc = List.filter (fun occ' -> not (subsumes occ occ')) acc in
        if List.exists (fun occ' -> subsumes occ' occ) acc
        then acc 
        else occ :: acc
      ) [] occs 
  in
  List.rev occs

(** Looks for timestamps at which macros occur in a term.
    Does not remove duplicates. 
    Over-approximation: we try to expand macros, even if they are at a timestamp 
    that may not happen. *)
let get_actions_ext : 
  type a. Constr.trace_cntxt -> a Term.term -> macro_ts_occs = 
  fun constr t ->

  let rec get : 
    type a. a Term.term -> fv:Sv.t -> cond:Term.message -> macro_ts_occs =
    fun t ~fv ~cond ->
      match t with
      | Term.ForAll (evs, t)
      | Term.Exists (evs, t) -> 
        let evs, subst = Term.erefresh_vars `Global evs in
        let t = Term.subst subst t in
        get t ~fv:(Sv.union fv (Sv.of_list evs)) ~cond

      | Term.Seq (is, t) ->
        let is, subst = Term.refresh_vars `Global is in
        let t = Term.subst subst t in
        let fv = Sv.add_list fv is in
        get t ~fv ~cond

      | Term.Fun (fs, _, [c;t;e]) when fs = Term.f_ite -> 
        get ~fv ~cond c @
        get ~fv ~cond:(Term.mk_and cond c) t @
        get ~fv ~cond:(Term.mk_and cond (Term.mk_not c)) e

      | Term.Find (is, c, t, e) -> 
        let is, subst = Term.refresh_vars `Global is in
        let c, t = Term.subst subst c, Term.subst subst t in
        let fv1 = Sv.add_list fv is in

        get ~fv:fv1 ~cond c @
        get ~fv:fv1 ~cond:(Term.mk_and cond c) t @
        get ~fv:fv  ~cond:(Term.mk_and cond (Term.mk_not c)) e                

      | Term.Macro (m, l, ts) ->
        if l <> [] then failwith "Not implemented" ;

        let get_macro_default () =
          let ts = match Symbols.Macro.get_def m.s_symb constr.table with
            | Symbols.Input -> Term.Pred ts
            | _             -> ts
          in
          let occ = { 
            mtso_ts   = ts;
            mtso_vars = fv; 
            mtso_cond = cond; } 
          in
          [occ] @ get ~fv ~cond ts          
        in

        if Macros.is_defined m.s_symb ts constr.table then
          try
            let t = Macros.get_definition constr m ts in
            get ~fv ~cond t
          with Tactics.Tactic_soft_failure _ -> get_macro_default ()

        else get_macro_default ()


      | Term.Name _
      | Term.Fun _
      | Term.Pred _
      | Term.Action _
      | Term.Var _
      | Term.Diff _
      | Term.Atom _ -> 
        Term.tfold (fun (Term.ETerm t) occs -> get t ~fv ~cond @ occs) t []
  in
  get t ~fv:Sv.empty ~cond:Term.mk_true
