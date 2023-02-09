(** Deprecated, kept temporarily for use in older functions *)
(** Utilities for tactics exploiting a name's freshness. *)

open Utils

module SE = SystemExpr

module Sv = Vars.Sv
module Sp = Match.Pos.Sp

(*------------------------------------------------------------------*)
(** Exception raised when a forbidden occurrence of a name is found. *)
exception Deprecated_Name_found
(** Exception raised when a forbidden occurrence of a message variable
    is found. *)
exception Deprecated_Var_found

(** Exception raised when attempting to apply a tactic on something
    that should be a name but isn't. *)
exception Deprecated_Not_name

(*------------------------------------------------------------------*)
(** Deprecated. *)
class deprecated_find_name ~(cntxt:Constr.trace_cntxt) exact name = object (_self)
  inherit Iter.deprecated_iter_approx_macros ~exact ~cntxt as super

  method visit_message t = match t with
    | Term.Name (ns,_) -> if ns.s_symb = name then raise Deprecated_Name_found
    | Term.Var m
      when Vars.ty m <> Type.Timestamp && Vars.ty m <> Type.Index ->
      (* FEATURE: this function is only used in [SystemModifiers], where
         variables are probabbly fine, regardless of their types. *)
      raise Deprecated_Var_found
    | _ -> super#visit_message t
end

(** Deprecated, use [get_actions_ext]. *)
class deprecated_get_actions ~(cntxt:Constr.trace_cntxt) = object (_self)
  inherit Iter.deprecated_iter_approx_macros ~exact:false ~cntxt as super

  val mutable actions : Term.term list = []
  method get_actions = actions

  method visit_macro mn _args a =
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
type deprecated_name_occ = Term.term list Iter.occ

type deprecated_name_occs = deprecated_name_occ list

let deprecated_pp_name_occ fmt (occ : deprecated_name_occ) : unit =
  Iter.pp_occ (Fmt.list ~sep:Fmt.comma Term.pp) fmt occ

(** Looks for indices at which a name occurs.
    @raise Var_found if a term variable occurs in the term. *)
let deprecated_get_name_indices_ext
    ~(env:Env.t)
    ?(fv=[])
    (constr : Constr.trace_cntxt)
    (nsymb : Symbols.name)
    (t : Term.term)
  : deprecated_name_occs
  =
  let env fv =
    Env.update ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true fv) env.vars) env
  in
  let rec get (t : Term.term) ~(fv : Vars.vars) ~(cond : Term.terms) : deprecated_name_occs =
    match t with
    | _ when HighTerm.is_ptime_deducible ~const:`Exact ~si:false (env fv) t -> []

    | Var _ -> raise Deprecated_Var_found

    | Term.Name (ns,args) when ns.s_symb = nsymb ->
      let occ = Iter.{
          occ_cnt  = args;
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
type deprecated_ts_occ = Term.term Iter.occ

type deprecated_ts_occs = deprecated_ts_occ list

let deprecated_pp_ts_occ fmt (occ : deprecated_ts_occ) : unit = Iter.pp_occ Term.pp fmt occ

(** Check if [t1] is included in the patterm [pat2], i.e. [t1 ∈ occ2]. *)
let deprecated_pat_subsumes
    table (context : SE.context)
    ?(mv : Match.Mvar.t = Match.Mvar.empty)
    (t1 : Term.term) (pat2 : Term.term Term.pat) 
  : Match.Mvar.t option
  =
  match Match.T.try_match ~mv table context t1 pat2
  with
  | FreeTyv | NoMatch _ -> None
  | Match mv -> Some mv

(** Check if the term occurrence [occ2] subsumes [occ1], i.e. [occ1 ⊆ occ2]. *)
let[@warning "-27"] deprecated_term_occ_subsumes
    table (context : SE.context)
    ?(mv : Match.Mvar.t = Match.Mvar.empty)
    (occ1 : Term.term Iter.occ) (occ2 : Term.term Iter.occ) 
  : bool
  =
  (* for now, positions not allowed here *)
  assert (Sp.is_empty occ1.occ_pos && Sp.is_empty occ2.occ_pos);

  let pat2 = Term.{
      pat_term   = occ2.occ_cnt;
      pat_tyvars = [];
      pat_vars   = Vars.Tag.local_vars occ2.occ_vars; 
    } in
  match deprecated_pat_subsumes table context occ1.occ_cnt pat2 with
  | None -> false
  | Some mv ->
    (* start from the matching substutition [mv], and try to match all
       conditions of [pat1.occ_conds] with a conditions of
       [pat2.occ_conds], updating [mv] along the way if successful. *)
    let mv = ref mv in

    let mk_cond2 cond2 = Term.{ pat2 with pat_term = cond2; } in
    List.for_all (fun cond1 ->
        List.exists (fun cond2 ->
            match 
              deprecated_pat_subsumes ~mv:(!mv) table context cond1 (mk_cond2 cond2)
            with 
            | None -> false
            | Some mv' -> mv := mv'; true
          ) occ2.occ_cond
      ) occ1.occ_cond


(** remove duplicates from [occs] using a subsuming relation. *)
let deprecated_remove_duplicate_term_occs
    table (system : SE.arbitrary)
    (occs : Term.term Iter.occs) : Term.term Iter.occs
  =
  let subsumes (occ1 : Term.term Iter.occ) (occ2 : deprecated_ts_occ) =
    let context = SE.{ set = system; pair = None; } in
    deprecated_term_occ_subsumes table context occ1 occ2
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
let deprecated_get_actions_ext (constr : Constr.trace_cntxt) (t : Term.term) : deprecated_ts_occs =

  let rec get (t : Term.term) ~(fv:Vars.vars) ~(cond:Term.terms) : deprecated_ts_occs =
    match t with
    | Term.Macro (m, l, ts) ->
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
        [occ] @ 
        List.concat_map (get ~fv ~cond) (ts :: l)
      in

      begin match Macros.get_definition constr m ~args:l ~ts with
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
let deprecated_get_macro_actions
    (cntxt : Constr.trace_cntxt)
    (sources : Term.terms) : deprecated_ts_occs
  =
  let actions =
    List.concat_map (deprecated_get_actions_ext cntxt) sources
  in
  deprecated_remove_duplicate_term_occs
    cntxt.table (cntxt.system :> SE.arbitrary) actions

(** [mk_le_ts_occ env ts0 occ] build a condition stating that [ts0] occurs
    before the macro timestamp occurrence [occ]. *)
let deprecated_mk_le_ts_occ
    (ts0 : Term.term)
    (occ : deprecated_ts_occ) : Term.term
  =
  let occ_vars = occ.Iter.occ_vars in
  let occ_vars, occ_subst = Term.refresh_vars occ_vars in
  let subst = occ_subst in
  let ts   = Term.subst subst occ.occ_cnt  in

  let cond = List.map (Term.subst subst) occ.occ_cond in
  let cond = List.rev cond in
  
  Term.mk_exists ~simpl:true occ_vars
    (Term.mk_and
       (Term.mk_timestamp_leq ts0 ts)
       (Term.mk_ands cond))

let deprecated_mk_le_ts_occs
    (ts0 : Term.term)
    (occs : deprecated_ts_occs) : Term.terms
  =
  List.map (deprecated_mk_le_ts_occ ts0) occs |>
  List.remove_duplicate (=)
