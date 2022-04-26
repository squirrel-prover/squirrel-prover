(** Utilities for tactics exploiting a name's freshness. *)

open Utils

module Sv = Vars.Sv
module Sp = Match.Pos.Sp

(*------------------------------------------------------------------*)
(** Exception raised when a forbidden occurrence of a name is found. *)
exception Name_found

(** Exception raised when a forbidden occurrence of a message variable
    is found. *)
exception Var_found

(** Exception raised when attempting to apply a tactic on something
    that should be a name but isn't. *)
exception Not_name

(*------------------------------------------------------------------*)
class find_name ~(cntxt:Constr.trace_cntxt) exact name = object (self)
  inherit Iter.iter_approx_macros ~exact ~cntxt as super

  method visit_message t = match t with
    | Term.Name ns -> if ns.s_symb = name then raise Name_found
    | Term.Var m
        when Vars.ty m <> Type.Timestamp && Vars.ty m <> Type.Index -> 
        raise Var_found
    | _ -> super#visit_message t
end

class get_name_indices ~(cntxt:Constr.trace_cntxt) exact name = object (self)
  inherit Iter.iter_approx_macros ~exact ~cntxt as super

  val mutable indices : (Vars.var list) list = []
  method get_indices = List.sort_uniq Stdlib.compare indices

  method visit_message t = match t with
    | Term.Name ns ->
      if ns.s_symb = name then indices <- ns.s_indices :: indices

    | Term.Var m -> raise Var_found

    | _ -> super#visit_message t
end

class get_actions ~(cntxt:Constr.trace_cntxt) = object (self)
  inherit Iter.iter_approx_macros ~exact:false ~cntxt as super

  val mutable actions : Term.term list = []
  method get_actions = actions

  method visit_macro mn a =
    let cleara, a' = match Symbols.Macro.get_def mn.s_symb cntxt.table with
      | Symbols.Input -> true,  Term.mk_pred a
      | _             -> false, a
    in
    if not (List.mem a' actions) then
      actions <- a' :: actions;

    (* remove [(a,false)] if it appeared in [actions] *)
    if cleara then
      actions <- List.filter (fun a0 -> a0 <> a) actions
 end

(*------------------------------------------------------------------*)
(** occurrence of a name [n(i,...,j)] *)
type name_occ = Vars.var list Iter.occ

type name_occs = name_occ list

let pp_name_occ fmt (occ : name_occ) : unit =
  Iter.pp_occ (Fmt.list ~sep:Fmt.comma Vars.pp) fmt occ

(** Looks for indices at which a name occurs.
    @raise Var_found if a term variable occurs in the term. *)
let get_name_indices_ext 
    ?(fv=[])
    (constr : Constr.trace_cntxt)
    (nsymb : Symbols.name)
    (t : Term.term)
  : name_occs
  =
  let rec get (t : Term.term) ~(fv : Vars.vars) ~(cond : Term.terms) : name_occs =
    match t with
    | Term.Var v when not (Type.is_finite (Vars.ty v)) ->
      raise Var_found

    | Term.Name ns when ns.s_symb = nsymb ->
      let occ = Iter.{
          occ_cnt  = ns.s_indices;
          occ_vars = List.rev fv;
          occ_cond = cond;
          occ_pos  = Sp.empty; }
      in
      [occ]

    | _ ->
      Iter.tfold_occ ~mode:(`Delta constr)
        (fun ~fv ~cond t occs ->
           get t ~fv ~cond @ occs
        ) ~fv ~cond t []
  in
  get t ~fv ~cond:[]

(*------------------------------------------------------------------*)
type ts_occ = Term.term Iter.occ

type ts_occs = ts_occ list

let pp_ts_occ fmt (occ : ts_occ) : unit = Iter.pp_occ Term.pp fmt occ


(** remove duplicates from occs for some subsuming relation. *)
let clear_dup_mtso_le (occs : ts_occs) : ts_occs =
  let subsumes (occ1 : ts_occ) (occ2 : ts_occ) =
    (* for now, positions not allowed here *)
    assert (Sp.is_empty occ1.occ_pos && Sp.is_empty occ2.occ_pos);
    
    (* TODO: alpha-renaming *)
    List.length occ1.occ_vars = List.length occ2.occ_vars &&
    List.for_all2 (=) occ1.occ_vars occ2.occ_vars &&
    occ1.occ_cond = occ2.occ_cond &&
    (occ1.occ_cnt = occ2.occ_cnt || occ1.occ_cnt = Term.mk_pred occ2.occ_cnt)
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

(** Looks for timestamps at which macros occur in a term. *)
let get_actions_ext (constr : Constr.trace_cntxt) (t : Term.term) : ts_occs =

  let rec get (t : Term.term) ~(fv:Vars.vars) ~(cond:Term.terms) : ts_occs =
    match t with
    | Term.Macro (m, l, ts) ->
      if l <> [] then failwith "Not implemented" ;

      let get_macro_default () =
        let ts = match Symbols.Macro.get_def m.s_symb constr.table with
          | Symbols.Input -> Term.mk_pred ts
          | _             -> ts
        in
        let occ = Iter.{
            occ_cnt  = ts;
            occ_vars = List.rev fv;
            occ_cond = cond;
            occ_pos  = Sp.empty; }
        in
        [occ] @ get ~fv ~cond ts
      in

      begin match Macros.get_definition constr m ts with
        | `Def t -> get ~fv ~cond t
        | `Undef | `MaybeDef -> get_macro_default ()
      end

    | _ ->
      (* Remark: we use [`NoDelta] because we want to have a different
         behavior depending on whether the macro can be expended or not. *)
      Iter.tfold_occ ~mode:`NoDelta
        (fun ~fv ~cond t occs ->
           get t ~fv ~cond @ occs
        ) ~fv ~cond t []
  in
  get t ~fv:[] ~cond:[]


(*------------------------------------------------------------------*)
(** Macro occurrence utility functions *)

(** Return timestamps occuring in macros in a set of terms *)
let get_macro_actions
    (cntxt : Constr.trace_cntxt)
    (sources : Term.terms) : ts_occs
  =
  let actions =
    List.concat_map (get_actions_ext cntxt) sources
  in
  clear_dup_mtso_le actions

(** [mk_le_ts_occ env ts0 occ] build a condition stating that [ts0] occurs
    before the macro timestamp occurrence [occ]. *)
let mk_le_ts_occ
    (env : Vars.env)
    (ts0 : Term.term)
    (occ : ts_occ) : Term.term
  =
  let occ_vars = occ.Iter.occ_vars in
  let occ_vars, occ_subst = Term.refresh_vars (`InEnv (ref env)) occ_vars in
  let subst = occ_subst in
  let ts   = Term.subst subst occ.occ_cnt  in

  let cond = List.map (Term.subst subst) occ.occ_cond in
  let cond = List.rev cond in
  
  Term.mk_exists ~simpl:true occ_vars
    (Term.mk_and
       (Term.mk_timestamp_leq ts0 ts)
       (Term.mk_ands cond))

let mk_le_ts_occs
    (env : Vars.env)
    (ts0 : Term.term)
    (occs : ts_occs) : Term.terms
  =
  List.map (mk_le_ts_occ env ts0) occs |>
  List.remove_duplicate (=)
