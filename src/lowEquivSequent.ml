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

      let pp_hyp = Equiv.pp
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
  hint_db : Hint.hint_db;
}



type sequent = t

type sequents = sequent list


let pp_goal fmt = function
  | Equiv.Atom (Equiv.Equiv e) -> Equiv.pp_equiv_numbered fmt e
  | _  as f -> Equiv.pp fmt f

let pp ppf j =
  Fmt.pf ppf "@[<v 0>" ;
  Fmt.pf ppf "@[Systems: %a@]@;"
    SystemExpr.pp_context j.env.system;

  if j.env.ty_vars <> [] then
    Fmt.pf ppf "@[Type variables: %a@]@;"
      (Fmt.list ~sep:Fmt.comma Type.pp_tvar) j.env.ty_vars ;

  if j.env.vars <> Vars.empty_env then
    Fmt.pf ppf "@[Variables: %a@]@;" Vars.pp_env j.env.vars ;

  H.pps ppf j.hyps ;

  (* Print separation between hyps and conclusion *)
  Printer.kws `Separation ppf (String.make 40 '-') ;
  Fmt.pf ppf "@;%a@]" pp_goal j.goal

let pp_init ppf j =
  if j.env.vars <> Vars.empty_env then
    Fmt.pf ppf "forall %a,@ " Vars.pp_env j.env.vars ;
  Fmt.pf ppf "%a" Equiv.pp j.goal


(*------------------------------------------------------------------*)
(** {2 Hypotheses functions} *)

(** Built on top of [H] *)
module Hyps
  : Hyps.HypsSeq with type hyp = Equiv.form and type sequent = t
 = struct
  type hyp = Equiv.form

  type ldecl = Ident.t * hyp

  type sequent = t

  let pp_hyp = Term.pp
  let pp_ldecl = H.pp_ldecl

  (* FIXME: move in hyps.ml, and get rid of duplicate in traceSequent.ml *)
  let fresh_id ?(approx=false) name s =
    let id = H.fresh_id name s.hyps in
    if (not approx) && Ident.name id <> name && name <> "_"
    then Tactics.soft_failure (T.HypAlreadyExists name)
    else id

  let fresh_ids ?(approx=false) names s =
    let ids = H.fresh_ids names s.hyps in

    if approx then ids else
      begin
        List.iter2 (fun id name ->
            if Ident.name id <> name && name <> "_"
            then Tactics.soft_failure (T.HypAlreadyExists name)
          ) ids names;
        ids
      end

  let is_hyp f s = H.is_hyp f s.hyps

  let by_id   id s = H.by_id   id s.hyps
  let by_name id s = H.by_name id s.hyps

  let mem_id   id s = H.mem_id   id s.hyps
  let mem_name id s = H.mem_name id s.hyps

  let find_opt func s = H.find_opt func s.hyps

  let find_map func s = H.find_map func s.hyps

  let to_list s = H.to_list s.hyps

  let exists func s = H.exists func s.hyps

  let add_formula ~force id (h : hyp)(s : sequent) =
    let id, hyps = H.add ~force id h s.hyps in
    id, { s with hyps = hyps }

  let add_i npat f s =
    let force, approx, name = match npat with
      | Args.Unnamed  -> true, true, "_"
      | Args.AnyName  -> false, true, "H"
      | Args.Named s  -> true, false, s
      | Args.Approx s -> true, true, s
    in
    let id = fresh_id ~approx name s in

    add_formula ~force id f s

  let add npat (f : hyp) s : sequent = snd (add_i npat f s)

  let add_i_list l (s : sequent) =
    let s, ids = List.fold_left (fun (s, ids) (npat,f) ->
        let id, s = add_i npat f s in
        s, id :: ids
      ) (s,[]) l in
    List.rev ids, s

  let add_list l s = snd (add_i_list l s)

  let remove id s = { s with hyps = H.remove id s.hyps }

  let fold func s init = H.fold func s.hyps init

  let map  f s = { s with hyps = H.map f s.hyps }
  let mapi f s = { s with hyps = H.mapi f s.hyps }

  let filter f s = { s with hyps = H.filter f s.hyps }

  let clear_triv s = s

  let pp fmt s = H.pps fmt s.hyps
  let pp_dbg fmt s = H.pps ~dbg:true fmt s.hyps
end

(*------------------------------------------------------------------*)
(** {2 Accessors and utils} *)

let update ?table ?ty_vars ?vars ?hyps ?goal t =
  let env  = Env.update ?table ?ty_vars ?vars t.env
  and hyps = Utils.odflt t.hyps hyps
  and goal = Utils.odflt t.goal goal in
  { t with env; hyps; goal; } 

let env j = j.env

let set_env env s = { s with env }

let vars j = j.env.vars

let set_vars vars j = update ~vars j

let system j = j.env.system
let set_system system j =
  let env = Env.set_system j.env system in
  { j with env }

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

(*------------------------------------------------------------------*)
let goal_is_equiv s = match goal s with
  | Atom (Equiv.Equiv e) -> true
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
  let hint_db = s.hint_db in

  let goal = match s.goal with
    | Equiv.Atom (Equiv.Reach f) -> f
    | _ ->
      Tactics.soft_failure
        (Tactics.GoalBadShape "expected a reachability formula")
  in

  let trace_s = TS.init ~env ~hint_db goal in
  Hyps.fold
    (fun id hyp trace_s ->
        TS.Hyps.add (Args.Named (Ident.name id)) (`Equiv hyp) trace_s)
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
  if Config.post_quantum () then
   check_pq_sound_sequent new_sequent
  else new_sequent


let init ~env ~hint_db ?hyp goal =
  let hyps = H.empty in
  let hyps = match hyp with
    | None -> hyps
    | Some h ->
        snd (H.add ~force:false (H.fresh_id "H" hyps) h hyps)
  in
  let new_sequent = { env; hint_db; hyps; goal } in
  if Config.post_quantum () then
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

let get_hint_db s = s.hint_db

(*------------------------------------------------------------------*)
let map f s : sequent =
  let f x = f.Equiv.Babel.call Equiv.Global_t x in
  set_goal (f (goal s)) (Hyps.map f s)

(*------------------------------------------------------------------*)
let fv s : Vars.Sv.t =
  let h_vars =
    Hyps.fold (fun _ f vars ->
        Vars.Sv.union (Equiv.fv f) vars
      ) s Vars.Sv.empty
  in
  Vars.Sv.union h_vars (Equiv.fv (goal s))

(*------------------------------------------------------------------*)
module Conc  = Equiv.Smart
module Hyp   = Equiv.Smart
