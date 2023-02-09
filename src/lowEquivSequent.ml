open Utils

module L = Location
module Args = TacticsArgs
module T = Tactics

module SE = SystemExpr
module TS = LowTraceSequent

(*------------------------------------------------------------------*)
(** {2 Hypotheses for equivalence sequents} *)

module H = Hyps.Mk
    (struct
      type t = Equiv.form

      let pp_hyp     = Equiv.pp
      let _pp_hyp    = Equiv._pp
      let pp_hyp_dbg = Equiv.pp_dbg

      let choose_name _f = "H"
        
      let htrue = Equiv.Atom (Equiv.Equiv [])
    end)

let subst_hyps (subst : Term.subst) (hyps : H.hyps) : H.hyps =
  H.map (Equiv.subst subst) hyps

(*------------------------------------------------------------------*)
(** {2 Equivalence sequent} *)

type hyp_form = Equiv.form
type conc_form = Equiv.form

let hyp_kind = Equiv.Global_t
let conc_kind = Equiv.Global_t

(* default variable information of the sequent *)
let var_info = Vars.Tag.gtag
    
(** An equivalence sequent features:
  * - two frames given as a single [goal] containing bi-terms
  *   of sort boolean or message;
  * - an environment [env] listing all free variables with their types;
  * - identifiers for the left and right systems.
  * The corresponding equivalence is obtained by projecting the bi-frame
  * to two frames, interpreting macros wrt the left and right systems
  * respectively. *)
type t = {
  env     : Env.t;
  hyps    : H.hyps;
  goal    : Equiv.form;
}

type sequent = t

type sequents = sequent list

(*------------------------------------------------------------------*)
let fv (s : t) : Vars.Sv.t =
  let h_vars =
    H.fold (fun _ f vars ->
        Vars.Sv.union (Equiv.fv f) vars
      ) s.hyps Vars.Sv.empty
  in
  Vars.Sv.union h_vars (Equiv.fv s.goal)

let sanity_check (s : t) : unit =
  Vars.sanity_check s.env.Env.vars;
  assert (Vars.Sv.subset (fv s) (Vars.to_vars_set s.env.Env.vars))

(*------------------------------------------------------------------*)
let _pp_goal ~dbg fmt = function
  | Equiv.Atom (Equiv.Equiv e) -> (Equiv._pp_equiv_numbered ~dbg) fmt e
  | _  as f -> Equiv._pp ~dbg fmt f

(*------------------------------------------------------------------*)
let _pp ~dbg ppf j =
  Fmt.pf ppf "@[<v 0>" ;
  Fmt.pf ppf "@[Systems: %a@]@;"
    SystemExpr.pp_context j.env.system;

  if j.env.ty_vars <> [] then
    Fmt.pf ppf "@[Type variables: %a@]@;"
      (Fmt.list ~sep:Fmt.comma Type.pp_tvar) j.env.ty_vars ;

  if j.env.vars <> Vars.empty_env then
    Fmt.pf ppf "@[Variables: %a@]@;" (Vars._pp_env ~dbg) j.env.vars ;

  H._pp ~dbg ppf j.hyps ;

  (* Print separation between hyps and conclusion *)
  Printer.kws `Separation ppf (String.make 40 '-') ;
  Fmt.pf ppf "@;%a@]" (_pp_goal ~dbg) j.goal

let pp     = _pp ~dbg:false
let pp_dbg = _pp ~dbg:true

(*------------------------------------------------------------------*)
let pp_init ppf j =
  if j.env.vars <> Vars.empty_env then
    Fmt.pf ppf "forall %a,@ " Vars.pp_env j.env.vars ;
  Fmt.pf ppf "%a" Equiv.pp j.goal


(*------------------------------------------------------------------*)
(** {2 Hypotheses functions} *)

(** Built on top of [H] *)
module Hyps
  : Hyps.S1 with type hyp = Equiv.form and type hyps := t
 = struct
  type hyp = Equiv.form

  type ldecl = Ident.t * hyp

  type sequent = t
    
  let pp_hyp = Equiv.pp

  let pp_ldecl = H.pp_ldecl

  let fresh_id  ?approx name  s = H.fresh_id  ?approx name  s.hyps
  let fresh_ids ?approx names s = H.fresh_ids ?approx names s.hyps

  let is_hyp f s = H.is_hyp f s.hyps

  let by_id   id s = H.by_id   id s.hyps
  let by_name id s = H.by_name id s.hyps

  let mem_id   id s = H.mem_id   id s.hyps
  let mem_name id s = H.mem_name id s.hyps

  let find_opt func s = H.find_opt func s.hyps

  let find_map func s = H.find_map func s.hyps

  let find_all func s = H.find_all func s.hyps
      
  let to_list s = H.to_list s.hyps

  let exists func s = H.exists func s.hyps

  let _add ~(force:bool) id hyp s =
    let id, hyps = H._add ~force id hyp s.hyps in
    id, { s with hyps }

  let add_i npat f s =
    let id, hyps = H.add_i npat f s.hyps in
    id, { s with hyps }

  let add npat (f : hyp) s : sequent = { s with hyps = H.add npat f s.hyps }

  let add_i_list l (s : sequent) =
    let ids, hyps = H.add_i_list l s.hyps in
    ids, { s with hyps }

  let add_list l s = { s with hyps = H.add_list l s.hyps }

  let remove id s = { s with hyps = H.remove id s.hyps }

  let fold func s init = H.fold func s.hyps init

  let map  f s = { s with hyps = H.map f s.hyps }
  let mapi f s = { s with hyps = H.mapi f s.hyps }

  let filter f s = { s with hyps = H.filter f s.hyps }

  let clear_triv s = { s with hyps = H.clear_triv s.hyps }

  let pp          fmt s = H.pp          fmt s.hyps
  let _pp    ~dbg fmt s = H._pp    ~dbg fmt s.hyps
  let pp_dbg      fmt s = H.pp_dbg      fmt s.hyps
end

(*------------------------------------------------------------------*)
(** {2 Accessors and utils} *)

let update ?table ?ty_vars ?vars ?hyps ?goal t =
  let env  = Env.update ?table ?ty_vars ?vars t.env
  and hyps = Utils.odflt t.hyps hyps
  and goal = Utils.odflt t.goal goal in
  { env; hyps; goal; } 

let env j = j.env

let set_env env s = { s with env }

let vars j = j.env.vars

let set_vars vars j = update ~vars j

let system j = j.env.system

let set_goal_in_context ?update_local system conc s =

  assert (update_local = None);

  if system = s.env.system then { s with goal = conc } else

    (* Update hypotheses.
       We add back manually all formulas, to ensure that definitions are
       unrolled. TODO really necessary? *)
    let _update_local,update_global =
      LowSequent.setup_set_goal_in_context
        ~table:s.env.table
        ~vars:s.env.vars
        ~old_context:s.env.system
        ~new_context:system
    in
    let s =
      H.fold
        (fun id f s ->
           match update_global f with
           | Some f ->
             let _,hyps = H._add ~force:true id f s.hyps in
             { s with hyps }
           | None -> s)
        s.hyps
        { s with hyps = H.empty }
    in

    (* Change the context in the sequent's environment. *)
    let env = Env.update ~system s.env in
    let s = { s with env } in

    (* Finally set the new conclusion. *)
    { s with goal = conc }

let table j = j.env.table
let set_table table j = update ~table j

let goal j = j.goal

let ty_vars j = j.env.ty_vars

let set_goal goal j = { j with goal }

let set_reach_goal f s = set_goal Equiv.(Atom (Reach f)) s

let get_frame proj j = match j.goal with
  | Equiv.Atom (Equiv.Equiv e) ->
    Some (List.map (Term.project1 proj) e)
  | _ -> None

let subst subst s =
  { s with goal = Equiv.subst subst s.goal;
           hyps = subst_hyps subst s.hyps; }


let rename (u:Vars.var) (v:Vars.var) (s:t) : t =
  assert (not (Vars.mem s.env.vars v));
  let s = subst [Term.ESubst (Term.mk_var u, Term.mk_var v)] s in
  let info = Vars.get_info u s.env.vars in
  {s with
    env = Env.update
             ~vars:(Vars.add_var v info (Vars.rm_var u s.env.vars))
             s.env;}

(*------------------------------------------------------------------*)
let goal_is_equiv s = match goal s with
  | Atom (Equiv.Equiv _) -> true
  | _ -> false

let goal_as_equiv s = match goal s with
  | Atom (Equiv.Equiv e) -> e
  | _ ->
    Tactics.soft_failure (Tactics.GoalBadShape "expected an equivalence")

(*------------------------------------------------------------------*)
(** Convert global sequent to local sequent, assuming
    that the conclusion of the input sequent is a local formula. *)
let to_trace_sequent s =
  let env = s.env in

  let goal = match s.goal with
    | Equiv.Atom (Equiv.Reach f) -> f
    | _ ->
      Tactics.soft_failure
        (Tactics.GoalBadShape "expected a reachability formula")
  in

  let trace_s = TS.init ~env goal in
  Hyps.fold
    (fun id hyp trace_s ->
        TS.Hyps.add (Args.Named (Ident.name id)) (Global hyp) trace_s)
    s trace_s

(*------------------------------------------------------------------*)
let get_trace_hyps s =
  TS.get_trace_hyps (to_trace_sequent (set_reach_goal Term.mk_false s))

(*------------------------------------------------------------------*)
let get_models (s : t) =
  let s = to_trace_sequent (set_reach_goal Term.mk_false s) in
  TS.get_models s

let mk_trace_cntxt ?(se : SE.fset option) (s : t) =
  let system = odflt (SE.to_fset s.env.system.set) se in
  Constr.{
    table  = s.env.table;
    system;
    models = Some (get_models s);
  }

(*------------------------------------------------------------------*)
let query_happens ~precise (s : t) (a : Term.term) =
  let s = to_trace_sequent (set_reach_goal Term.mk_false s) in
  TS.query_happens ~precise s a


let check_pq_sound_sequent s =
  match goal s with
  | Atom (Equiv.Equiv e) ->
      let models = get_models s in
      let cntxt = Constr.{
        table = s.env.table;
        system = (Utils.oget s.env.system.pair:>SystemExpr.fset);
        models = Some (get_models s)
      } in
      if not (PostQuantum.is_attacker_call_synchronized cntxt models e) then
        Tactics.hard_failure Tactics.GoalNotPQSound
      else
        s
  | _ -> s

(*------------------------------------------------------------------*)
let set_equiv_goal e j =
  let new_sequent = set_goal Equiv.(Atom (Equiv e)) j in
  if TConfig.post_quantum (table j) then
   check_pq_sound_sequent new_sequent
  else new_sequent


let init ~env ?hyp goal =
  let hyps = H.empty in
  let hyps = match hyp with
    | None -> hyps
    | Some h ->
        snd (H._add ~force:false (H.fresh_id "H" hyps) h hyps)
  in
  let new_sequent = { env; hyps; goal } in
  sanity_check new_sequent;

  if TConfig.post_quantum (env.table) then
   check_pq_sound_sequent new_sequent
  else new_sequent

let mem_felem i s =
  goal_is_equiv s &&
  i < List.length (goal_as_equiv s)

let change_felem ?loc i elems s =
  try
    let before, _, after = List.splitat i (goal_as_equiv s) in
    set_equiv_goal (List.rev_append before (elems @ after)) s
  with List.Out_of_range ->
    Tactics.soft_failure ?loc (Tactics.Failure "out of range position")


let get_felem ?loc i s =
  try
    let _, t, _ = List.splitat i (goal_as_equiv s) in t
  with List.Out_of_range ->
    Tactics.soft_failure ?loc (Tactics.Failure "out of range position")

(*------------------------------------------------------------------*)
let get_system_pair t = oget (system t).pair

let get_system_pair_projs t : Term.proj * Term.proj =
  let p = get_system_pair t in
  fst (SE.fst p), fst (SE.snd p)

(*------------------------------------------------------------------*)
let map f s : sequent =
  let f x = f.Equiv.Babel.call Equiv.Global_t x in
  set_goal (f (goal s)) (Hyps.map f s)


(*------------------------------------------------------------------*)
let mk_pair_trace_cntxt (s : sequent) : Constr.trace_cntxt =
  let se = (Utils.oget ((env s).system.pair) :> SE.fset) in
  mk_trace_cntxt ~se s 

let check_goal_is_equiv (s : sequent) : unit =
  if not (Equiv.is_equiv (goal s)) then
    Tactics.soft_failure (Tactics.GoalBadShape "expected an equivalence")


(*------------------------------------------------------------------*)
module Conc  = Equiv.Smart
module Hyp   = Equiv.Smart
