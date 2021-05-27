open Utils

module L = Location
module Args = TacticsArgs
module T = Tactics

module TS = LowTraceSequent

type lsymb = Theory.lsymb

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

type hyps = H.hyps

(*------------------------------------------------------------------*)
(** {2 Equivalence sequent} *)

type form = Equiv.form

let pp_form = Equiv.pp

(** An equivalence sequent features:
  * - two frames given as a single [goal] containing bi-terms
  *   of sort boolean or message;
  * - an environment [env] listing all free variables with their types;
  * - identifiers for the left and right systems.
  * The corresponding equivalence is obtained by projecting the bi-frame
  * to two frames, interpreting macros wrt the left and right systems
  * respectively. *)
type t = {
  env     : Vars.env;
  table   : Symbols.table;
  ty_vars : Type.tvars;
  hyps    : H.hyps;
  goal    : Equiv.form;
  system  : SystemExpr.system_expr;
  hint_db : Hint.hint_db;
}

let init system table hint env hyps f = {
  env     = env ; 
  table   = table ;
  ty_vars = [];
  goal    = f; 
  hyps    = hyps;
  system  = system;
  hint_db = hint;
}

type sequent = t

type sequents = sequent list


let pp_goal fmt = function
  | Equiv.Atom (Equiv.Equiv e) -> Equiv.pp_equiv_numbered fmt e
  | _  as f -> Equiv.pp fmt f
  
let pp ppf j =
  Fmt.pf ppf "@[<v 0>" ;
  Fmt.pf ppf "@[System: %a@]@;"
    SystemExpr.pp_system j.system;

  if j.ty_vars <> [] then
    Fmt.pf ppf "@[Type variables: %a@]@;" 
      (Fmt.list ~sep:Fmt.comma Type.pp_tvar) j.ty_vars ;

  if j.env <> Vars.empty_env then
    Fmt.pf ppf "@[Variables: %a@]@;" Vars.pp_env j.env ;

  H.pps ppf j.hyps ;

  (* Print separation between hyps and conclusion *)
  Fmt.styled `Bold Utils.ident ppf (String.make 40 '-') ;
  Fmt.pf ppf "@;%a@]" pp_goal j.goal

let pp_init ppf j =
  if j.env <> Vars.empty_env then
    Fmt.pf ppf "forall %a,@ " Vars.pp_env j.env ;
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
    then Hyps.hyp_error ~loc:None (T.HypAlreadyExists name) 
    else id

  let fresh_ids ?(approx=false) names s =
    let ids = H.fresh_ids names s.hyps in
    
    if approx then ids else
      begin
        List.iter2 (fun id name ->
            if Ident.name id <> name && name <> "_"
            then Hyps.hyp_error ~loc:None (T.HypAlreadyExists name)
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
      | Args.Unnamed -> true, true, "_"
      | Args.AnyName -> false, true, "H"
      | Args.Named s -> true, false, s in

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

  let clear_triv s = s

  let pp fmt s = H.pps fmt s.hyps
  let pp_dbg fmt s = H.pps ~dbg:true fmt s.hyps
end

(*------------------------------------------------------------------*)
(** {2 Accessors and utils} *)

let env j = j.env

let set_env e j = {j with env = e}

let system j = j.system
let set_system system j = { j with system }

let table j = j.table
let set_table table j = { j with table = table }

let goal j = j.goal

let ty_vars j = j.ty_vars

let hyps j = j.hyps

let set_hyps hyps j = { j with hyps }

let set_goal goal j = { j with goal }

let set_ty_vars ty_vars j = { j with ty_vars } 

let set_equiv_goal e j = { j with goal = Equiv.Atom (Equiv.Equiv e) }

let get_frame proj j = match j.goal with
  | Equiv.Atom (Equiv.Equiv e) -> 
    Some (List.map (Equiv.pi_term proj) e)
  | _ -> None

let subst subst s =
  { s with goal = Equiv.subst subst s.goal;
           hyps = subst_hyps subst s.hyps; }

let subst_hyp subst f = Equiv.subst subst f

(*------------------------------------------------------------------*)
let goal_is_equiv s = match goal s with
  | Atom (Equiv.Equiv e) -> true
  | _ -> false

let goal_as_equiv s = match goal s with
  | Atom (Equiv.Equiv e) -> e
  | _ -> 
    Tactics.soft_failure (Tactics.GoalBadShape "expected an equivalence")
      
let set_reach_goal f s = set_goal Equiv.(Atom (Reach f)) s

let reach_to_form t = Equiv.Atom (Equiv.Reach t)

let form_to_reach ?loc (e : Equiv.form) = 
  match e with
  | Equiv.Atom (Equiv.Reach f) -> f
  | _ ->     
    Tactics.soft_failure ?loc (Tactics.Failure "expected a reachability formula")

(*------------------------------------------------------------------*)
let trace_seq_of_equiv_seq ?goal s = 
  let env     = env s in
  let system  = system s in
  let table   = table s in
  let ty_vars = ty_vars s in
  let hint_db = s.hint_db in

  let goal = match goal, s.goal with
    | Some g, _ -> g
    | None, Equiv.Atom (Equiv.Reach f) -> f
    | None, _ -> 
      Tactics.soft_failure (Tactics.GoalBadShape "expected a reachability \
                                                  formulas")
  in

  let trace_s = TS.init ~system ~table ~hint_db ~ty_vars ~env ~goal in
  
  (* We add all relevant hypotheses *)
  Hyps.fold (fun id hyp trace_s -> match hyp with
      | Equiv.Atom (Equiv.Reach h) -> 
        TS.Hyps.add (Args.Named (Ident.name id)) h trace_s
      | _ -> trace_s
    ) s trace_s 

(*------------------------------------------------------------------*)
let get_trace_literals s = 
  TS.get_trace_literals (trace_seq_of_equiv_seq ~goal:Term.mk_false s)

(*------------------------------------------------------------------*)
let get_models (s : t) =
  let s = trace_seq_of_equiv_seq ~goal:Term.mk_false s in
  TS.get_models s

let mk_trace_cntxt (s : t) = 
  Constr.{
    table  = s.table;
    system = s.system;
    models = Some (get_models s);
  }

let trace_seq_of_reach f s = trace_seq_of_equiv_seq (set_reach_goal f s)

(*------------------------------------------------------------------*)
let rec get_terms (f : Equiv.form) : Term.message list =
  match f with
  | Equiv.Atom (Equiv.Reach f) -> [f]
  | Equiv.Atom (Equiv.Equiv e) -> e
  | Equiv.Impl (e1, e2) -> get_terms e1 @ get_terms e2
  | Equiv.ForAll (vs, e) -> []

(*------------------------------------------------------------------*)
let query_happens ~precise (s : t) (a : Term.timestamp) =
  let s = trace_seq_of_equiv_seq ~goal:Term.mk_false s in
  TS.query_happens ~precise s a

(*------------------------------------------------------------------*)
let mem_felem i s = 
  goal_is_equiv s && 
  i < List.length (goal_as_equiv s)
  
let change_felem i elems s =
  let before, _, after = List.splitat i (goal_as_equiv s) in
  set_equiv_goal (List.rev_append before (elems @ after)) s

let get_felem i s = let _, t, _ = List.splitat i (goal_as_equiv s) in t

let get_hint_db s = s.hint_db

(*------------------------------------------------------------------*)
let map f s : sequent = set_goal (f (goal s)) (Hyps.map f s)

(*------------------------------------------------------------------*)
(** {2 Matching} *)
module Match = Equiv.Match

(*------------------------------------------------------------------*)
module Smart = Equiv.Smart