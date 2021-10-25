module Sv = Vars.Sv

exception Name_found
exception Var_found
exception Not_name

class find_name ~(cntxt:Constr.trace_cntxt) exact name = object (self)
  inherit Iter.iter_approx_macros ~exact ~cntxt as super

  method visit_message t = match t with
    | Term.Name ns -> if ns.s_symb = name then raise Name_found
    | Term.Var m -> raise Var_found
    | _ -> super#visit_message t
end

class get_name_indices ~(cntxt:Constr.trace_cntxt) exact name = object (self)
  inherit Iter.iter_approx_macros ~exact ~cntxt as super

  val mutable indices : (Vars.index list) list = []
  method get_indices = List.sort_uniq Stdlib.compare indices

  method visit_message t = match t with
    | Term.Name ns -> 
      if ns.s_symb = name then indices <- ns.s_indices :: indices

    | Term.Var m -> raise Var_found

    | _ -> super#visit_message t
end

class get_actions ~(cntxt:Constr.trace_cntxt) = object (self)
  inherit Iter.iter_approx_macros ~exact:false ~cntxt as super

  val mutable actions : Term.timestamp list = []
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
type name_occ = Vars.index list Iter.occ

type name_occs = name_occ list

let pp_name_occ fmt (occ : name_occ) : unit = 
  Iter.pp_occ (Fmt.list ~sep:Fmt.comma Vars.pp) fmt occ

(** Looks for indices at which a name occurs.
    Raise @Var_found if a term variable occurs in the term. *)
let get_name_indices_ext : type a. 
  ?fv:Sv.t -> 
  Constr.trace_cntxt -> 
  Symbols.name Symbols.t -> 
  a Term.term -> 
  name_occs 
  = 
  fun ?(fv=Sv.empty) constr nsymb t ->

  let rec get : 
    type a. a Term.term -> fv:Sv.t -> cond:Term.message -> name_occs =
    fun t ~fv ~cond ->
      match t with
      | Term.Var v when Type.equalk (Vars.kind v) Type.KMessage -> 
        raise Var_found

      | Term.Name ns when ns.s_symb = nsymb ->
        let occ = Iter.{ 
            occ_cnt  = ns.s_indices;
            occ_vars = fv; 
            occ_cond = cond; } 
        in
        [occ]

      | _ -> 
        Iter.tfold_occ ~mode:(`Delta constr)
          (fun ~fv ~cond (Term.ETerm t) occs -> 
             get t ~fv ~cond @ occs
          ) ~fv ~cond t []
  in
  get t ~fv ~cond:Term.mk_true

(*------------------------------------------------------------------*)
type ts_occ = Term.timestamp Iter.occ

type ts_occs = ts_occ list

let pp_ts_occ fmt (occ : ts_occ) : unit = Iter.pp_occ Term.pp fmt occ


(** remove duplicates from occs for some subsuming relation. *)
let clear_dup_mtso_le (occs : ts_occs) : ts_occs = 
  let subsumes (occ1 : ts_occ) (occ2 : ts_occ) =
    (* TODO: alpha-renaming *)
    Sv.equal occ1.occ_vars occ2.occ_vars &&
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
let get_actions_ext : 
  type a. Constr.trace_cntxt -> a Term.term -> ts_occs = 
  fun constr t ->

  let rec get : 
    type a. a Term.term -> fv:Sv.t -> cond:Term.message -> ts_occs =
    fun t ~fv ~cond ->
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
            occ_vars = fv; 
            occ_cond = cond; } 
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
          (fun ~fv ~cond (Term.ETerm t) occs -> 
             get t ~fv ~cond @ occs
          ) ~fv ~cond t []
  in
  get t ~fv:Sv.empty ~cond:Term.mk_true
