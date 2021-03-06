(** All reachability tactics.
   Tactics are organized in three classes:
    - Logical -> relies on the logical properties of the sequent.
    - Strucutral -> relies on properties of protocols, or of equality over messages,...
    - Cryptographic -> relies on a cryptographic assumptions, that must be assumed.*)

open Term
open Utils

type tac = TraceSequent.t Tactics.tac

module T = Prover.TraceTactics

module Args = TacticsArgs

module L = Location

module Hyps = TraceSequent.Hyps

type lsymb = Theory.lsymb
type sequent = TraceSequent.sequent

(*------------------------------------------------------------------*)
let dbg ?(force=false) s =
  let mode = if Config.debug_tactics () || force then `Dbg else `Ignore in
  Printer.prt mode s

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
let get_models s = Tactics.timeout_get (TraceSequent.get_models s)
let get_trs    s = Tactics.timeout_get (TraceSequent.get_trs s)

(*------------------------------------------------------------------*)
let mk_trace_cntxt s = 
  Constr.{
    table  = TraceSequent.table s;
    system = TraceSequent.system s;
    models = Some (get_models s);
  }

(*------------------------------------------------------------------*)
let wrap_fail f (s: TraceSequent.t) sk fk =
  try sk (f s) fk with
  | Tactics.Tactic_soft_failure (_,e) -> fk e

(*------------------------------------------------------------------*)
(** {2 Logical Tactics} *)

(** Propositional connectives *)

(** Reduce a goal with a disjunction conclusion into the goal
  * where the conclusion has been replace with the first disjunct. *)
let goal_or_right_1 (s : TraceSequent.t) =
  match TraceSequent.conclusion s with
  | (Or (lformula, _)) -> [TraceSequent.set_conclusion (lformula) s]
  | _ -> soft_failure (Tactics.Failure "Cannot introduce a disjunction")

(** Reduce a goal with a disjunction conclusion into the goal
  * where the conclusion has been replace with the second disjunct. *)
let goal_or_right_2 (s : TraceSequent.t) =
  match TraceSequent.conclusion s with
  | (Or (_, rformula)) -> [TraceSequent.set_conclusion (rformula) s]
  | _ -> soft_failure (Tactics.Failure "Cannot introduce a disjunction")

let () =
  T.register "left"
    ~tactic_help:{general_help = "Reduce a goal with a disjunction conclusion \
                                  into the goal where the conclusion has been \
                                  replaced with the first disjunct.";
                  detailed_help = "G => A v B yields G => A";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    goal_or_right_1;

  T.register "right"
    ~tactic_help:{general_help = "Reduce a goal with a disjunction conclusion \
                                  into the goal where the conclusion has been \
                                  replace with the second disjunct.";
                  detailed_help = "G => A v B yields G => B";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    goal_or_right_2

(*------------------------------------------------------------------*)
let goal_true_intro (s : TraceSequent.t) =
  match TraceSequent.conclusion s with
  | True -> []
  | _ -> soft_failure (Tactics.Failure "Cannot introduce true")

let () =
  T.register "true"
     ~tactic_help:{general_help = "Solves a goal when the conclusion is true.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    goal_true_intro

(*------------------------------------------------------------------*)
let print_tac s =
  Tactics.print_system (TraceSequent.table s) (TraceSequent.system s);
  [s]

let () =
  T.register "print"
    ~tactic_help:{general_help = "Shows the current system.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    print_tac

(*------------------------------------------------------------------*)
(** Split a conjunction conclusion,
  * creating one subgoal per conjunct. *)
let goal_and_right (s : TraceSequent.t) =
  match TraceSequent.conclusion s with
  | And (lformula, rformula) ->
    [ TraceSequent.set_conclusion lformula s ;
      TraceSequent.set_conclusion rformula s ]
  | _ -> soft_failure (Tactics.Failure "Cannot introduce a conjunction")

let () =
  T.register "split"
    ~tactic_help:{general_help = "Split a conjunction conclusion, creating one \
                                  subgoal per conjunct.";
                  detailed_help = "G=> A & B is replaced by G=>A and goal G=>B.";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    goal_and_right


(*------------------------------------------------------------------*)
let left_not_intro (Args.String hyp_name) s =
  let id, formula = Hyps.by_name hyp_name s in
  let s = Hyps.remove id s in
  match formula with
  | Not f ->
    [Hyps.add (Args.Named (Ident.name id)) (Term.not_simpl f) s]

  | _ -> soft_failure (Tactics.Failure "cannot introduce negation")

let () =
  T.register_typed "notleft"
    ~general_help:"Push a negation inside a formula."
    ~detailed_help:"Normalize the formula according to the negation rules over \
                    logical connectors."
    ~tactic_group:Logical
    left_not_intro Args.String

(*------------------------------------------------------------------*)
(** Apply a naming pattern to a variable or hypothesis. *)
let do_naming_pat (ip_handler : Args.ip_handler) nip s : sequent =
  match ip_handler with
  | `Var Vars.EVar v ->
    let env = ref (TraceSequent.env s) in

    let v' = match nip with
      | Args.Unnamed
      | Args.AnyName ->
        Vars.make_fresh_from_and_update env v

      | Args.Named name ->
        let v' = Vars.make_fresh_and_update env (Vars.sort v) name in

        if Vars.name v' <> name then
          hard_failure (
            Tactics.Failure ("variable name " ^ name ^ " already in use"));
        v'
    in
    let subst = [Term.ESubst (Term.Var v, Term.Var v')] in

    (* FIXME: we substitute everywhere. This is inefficient. *)
    TraceSequent.subst subst (TraceSequent.set_env !env s)

  | `Hyp hid ->
    let f = Hyps.by_id hid s in
    let s = Hyps.remove hid s in

    Hyps.add nip f s

(*------------------------------------------------------------------*)
(** Type for case and destruct tactics handlers *)
type c_handler =
  | CHyp of Ident.t

type c_res = c_handler * sequent

(** Case analysis on a timestamp *)
let timestamp_case (ts : Term.timestamp) s : c_res list =
  let system = TraceSequent.system s in
  let table  = TraceSequent.table s in

  let mk_case descr =
    let indices =
      let env = ref @@ TraceSequent.env s in
      List.map
        (fun i -> Vars.make_fresh_from_and_update env i)
        descr.Action.indices in

    let subst =
      List.map2 (fun i i' -> Term.ESubst (Term.Var i,Term.Var i'))
        descr.Action.indices indices in

    let name =
      SystemExpr.action_to_term table system
        (Action.subst_action subst descr.Action.action) in
    let name = Term.subst subst name in

    let at = Term.Atom ((`Timestamp (`Eq,ts,name)) :> generic_atom) in

    if indices = [] then at else
      Exists (List.map (fun x -> Vars.EVar x) indices,at) 
  in

  let cases = SystemExpr.map_descrs table system mk_case in

  List.map (fun f ->
      let id, s = Hyps.add_i Args.Unnamed f s in
      ( CHyp id, s )
    ) cases

(** Case analysis on an hypothesis.
    When [nb=`Any], recurses. 
    When [nb=`Some l], destruct at most [l]. *)
let hypothesis_case ~nb id (s : TraceSequent.t) : c_res list =
  let destr_err () =
    soft_failure (Tactics.Failure "can only be applied to a disjunction")
  in

  let rec case acc = function
    | Or (f,g) -> case (case acc g) f
    | _ as f -> f :: acc in

  let form = Hyps.by_id id s in
  let s = Hyps.remove id s in

  let cases = match nb with
    | `Any -> case [] form 
    | `Some l -> match Term.destr_ors l form with
      | None -> destr_err ()
      | Some cases -> cases
  in

  if cases = [] then destr_err ();

  List.map (fun g ->
      let ng = Ident.name id in
      let idg, sg = Hyps.add_i (Args.Named ng) g s in
      ( CHyp idg, sg )
    ) cases


(** Case analysis on [orig = Find (vars,c,t,e)] in [s].
  * This can be used with [vars = []] if orig is an [if-then-else] term. *)
let case_cond orig vars c t e s =
  let env = ref (TraceSequent.env s) in
  let vars' = List.map (Vars.make_fresh_from_and_update env) vars in
  let subst =
    List.map2
      (fun i i' -> ESubst (Term.Var i, Term.Var i'))
      vars vars'
  in
  let c' = Term.(ForAll (List.map (fun i -> Vars.EVar i) vars, Not c)) in
  let c = Term.subst subst c in
  let t = Term.subst subst t in
  let then_subst = [ Term.ESubst (orig,t) ] in
  let else_subst = [ Term.ESubst (orig,e) ] in

  let idthen, sthen = Hyps.add_i Args.Unnamed c  s
  and idelse, selse = Hyps.add_i Args.Unnamed c' s in

  let sthen = TraceSequent.set_env !env sthen in

  [ ( CHyp idthen, TraceSequent.subst then_subst sthen );
    ( CHyp idelse, TraceSequent.subst else_subst selse ) ]

let message_case (m : Term.message) s : c_res list =
  begin match m with
    | Term.(Find (vars,c,t,e)) as o -> case_cond o vars c t e s
    | Term.(ITE (c,t,e)) as o -> case_cond o [] c t e s
    | Term.Macro ((m,Sorts.Message,is),[],ts) as o
      when Macros.is_defined m ts (TraceSequent.table s) ->
      if not (TraceSequent.query_happens ~precise:true s ts) 
      then soft_failure (Tactics.MustHappen ts)
      else
        begin match
            Macros.get_definition
              (mk_trace_cntxt s)
              Sorts.Message
              m is ts
          with
          | Term.(Find (vars,c,t,e)) -> case_cond o vars c t e s
          | Term.(ITE (c,t,e)) -> case_cond o [] c t e s
          | _ -> Tactics.(soft_failure (Failure "message is not a conditional"))
        end
    | _ ->
      Tactics.(soft_failure (Failure "message is not a conditional"))
    | exception _ ->
      Tactics.(soft_failure (Failure "improper argument"))
  end

let do_case_tac (args : Args.parser_arg list) s =
  match Args.convert_as_lsymb args with
  | Some str when Hyps.mem_name (L.unloc str) s ->
    let id, _ = Hyps.by_name str s in
    hypothesis_case ~nb:`Any id s

  | _ ->
    let env, tbl = TraceSequent.env s, TraceSequent.table s in
    match Args.convert_args tbl env args Args.(Sort ETerm) with
    | Args.Arg (ETerm (Sorts.Timestamp, f, loc)) ->
      timestamp_case f s
    | Args.Arg (ETerm (Sorts.Message, f, loc)) ->
      message_case f s
    | _ -> Tactics.(hard_failure (Failure "improper arguments"))

let case_tac (args : Args.parser_arg list) s
    (sk : TraceSequent.t list Tactics.sk) fk =
  try
    let cres = do_case_tac args s in
    let ss = List.map (fun (CHyp id, s) ->
        (* TODO: location *)
        do_naming_pat (`Hyp id) Args.AnyName s
      ) cres in
    sk ss fk
  with Tactics.Tactic_soft_failure (_,e) -> fk e

let () =
  let open Tactics in
  T.register_general "case"
    ~tactic_help:
      {general_help = "Perform case analysis on a timestamp, a message built \
                       using a conditional, or a disjunction hypothesis.";
       detailed_help = "A timestamp will be instantiated by all \
                        possible actions, a disjunction hypothesis A \
                        v B => C will produce two goals A => B and B \
                        => C, and a message with a conditional will \
                        be split into the two branches.";
       usages_sorts = [Sort Args.Timestamp;
                       Sort Args.String;
                       Sort Args.Message];
       tactic_group = Logical}
    case_tac



(*------------------------------------------------------------------*)
let false_left s =
  if Hyps.exists (fun _ f -> match f with False -> true | _ -> false) s
  then []
  else Tactics.(soft_failure (Failure "no False assumption"))

let () =
  T.register "false_left"
     ~tactic_help:{general_help = "Closes a goal when False is among its assumptions.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    false_left

(*------------------------------------------------------------------*)
let revert (hid : Ident.t) s =
  let f = Hyps.by_id hid s in
  let s = Hyps.remove hid s in
  TraceSequent.set_conclusion (Term.Impl (f,TraceSequent.conclusion s)) s

let revert_str (hyp_name : lsymb) s =
  let hid,_ = Hyps.by_name hyp_name s in
  revert hid s

let revert_tac (args : Args.parser_arg list) s sk fk = 
  try
    let s = 
      List.fold_left (fun s arg -> match arg with
          | Args.String_name arg -> revert_str arg s
          | _ -> hard_failure (Failure "improper arguments")
        ) s args in
    sk [s] fk
  with Tactics.Tactic_soft_failure (_,e) -> fk e
      
let () =
  T.register_general "revert"
    ~tactic_help:{
      general_help = "Take an hypothesis H, and turns the conclusion C into the \
                      implication H => C.";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    revert_tac


(*------------------------------------------------------------------*)
let clear (hid : Ident.t) s = Hyps.remove hid s

let clear_str (hyp_name : lsymb) s =
  let hid,_ = Hyps.by_name hyp_name s in
  clear hid s

let clear_tac (args : Args.parser_arg list) s sk fk = 
  try
    let s = 
      List.fold_left (fun s arg -> match arg with
          | Args.String_name arg -> clear_str arg s
          | _ -> hard_failure (Failure "improper arguments")
        ) s args in
    sk [s] fk
  with Tactics.Tactic_soft_failure (_,e) -> fk e
      
let () =
  T.register_general "clear"
    ~tactic_help:{
      general_help = "Clear an hypothesis.";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    clear_tac


(*------------------------------------------------------------------*)
(** Apply a And pattern (this is a destruct) of length [l].
    Note that variables in handlers have not been added to the env yet. *)
let do_and_pat (hid : Ident.t) len s : Args.ip_handler list * sequent =
  let destr_fail s = 
    soft_failure (Tactics.Failure ("cannot destruct: " ^ s)) 
  in
  let get_destr ~orig = function
    | Some x -> x
    | None -> destr_fail (Fmt.str "%a" Term.pp orig) in

  assert (len > 0);
  if len = 1 then ([`Hyp hid], s) else
    let form = Hyps.by_id hid s in
    let s = Hyps.remove hid s in

    match form with
    | Term.Atom at ->
      begin
        match Term.destr_atom at with
        | Term.EOrd (`Eq,a,b) ->
          let a1, a2 = get_destr ~orig:a (destr_pair a)
          and b1, b2 = get_destr ~orig:b (destr_pair b) in

          let f1 = Atom (Term.of_eatom (Term.EOrd (`Eq, a1, b1)))
          and f2 = Atom (Term.of_eatom (Term.EOrd (`Eq, a2, b2))) in

          let forms = List.map (fun x -> Args.Unnamed, x) [f1;f2] in
          let ids, s = Hyps.add_i_list forms s in
          List.map (fun id -> `Hyp id) ids, s

        | Term.EOrd (_,_,_) 
        | Term.EHappens _ -> 
          destr_fail (Fmt.str "%a" Term.pp form)
      end

    | Term.And _ ->
      let ands = get_destr ~orig:form (Term.destr_ands len form) in
      let ands = List.map (fun x -> Args.Unnamed, x) ands in
      let ids, s = Hyps.add_i_list ands s in
      List.map (fun id -> `Hyp id) ids, s

    | Term.Exists _ ->
      let vs, f = get_destr ~orig:form (Term.destr_exists form) in

      if List.length vs < len - 1 then
        hard_failure (Tactics.PatNumError (len - 1, List.length vs));

      let vs, vs' = List.takedrop (len - 1) vs in
      let vs_fresh, subst = 
        List.split (
          List.map (fun (Vars.EVar v) -> 
              let v_f = Vars.make_new_from v in
              Vars.EVar v_f, Term.ESubst (Var v, Var v_f)
            ) vs)
      in
      let f = Term.mk_exists vs' f in
      let f = Term.subst subst f in

      let idf, s = Hyps.add_i Args.Unnamed f s in

      ( (List.map (fun x -> `Var x) vs_fresh) @ [`Hyp idf], s )

    | _ -> destr_fail (Fmt.str "cannot destruct %a" Term.pp form)

(** Apply an And/Or pattern to an ident hypothesis handler. *)
let rec do_and_or_pat (hid : Ident.t) (pat : Args.and_or_pat) s
  : sequent list =
  match pat with
  | Args.And s_ip ->
    (* Destruct the hypothesis *)
    let handlers, s = do_and_pat hid (List.length s_ip) s in

    if List.length handlers <> List.length s_ip then
      hard_failure (Tactics.PatNumError (List.length s_ip, List.length handlers));

    (* Apply, for left to right, the simple patterns, and collect everything *)
    let ss = List.fold_left2 (fun ss handler ip ->
        List.map (do_simpl_pat handler ip) ss
        |> List.flatten
      ) [s] handlers s_ip in
    ss

  | Args.Or s_ip ->
    let ss = hypothesis_case ~nb:(`Some (List.length s_ip)) hid s in

    if List.length ss <> List.length s_ip then
      hard_failure (Tactics.PatNumError (List.length s_ip, List.length ss));

    (* For each case, apply the corresponding simple pattern *)
    List.map2 (fun (CHyp id, s) ip ->
        do_simpl_pat (`Hyp id) ip s
      ) ss s_ip

    (* Collect all cases *)
    |> List.flatten

  | Args.Split ->
    (* Destruct many Or *)
    let ss = hypothesis_case ~nb:`Any hid s in

    (* For each case, apply the corresponding simple pattern *)
    List.map (fun (CHyp id, s) ->
        revert id s
      ) ss

(** Apply an simple pattern a handler. *)
and do_simpl_pat (h : Args.ip_handler) (ip : Args.simpl_pat) s
  : sequent list =
  match h, ip with
  | _, Args.SNamed n_ip -> [do_naming_pat h n_ip s]

  | `Var _, Args.SAndOr ao_ip ->
    hard_failure (Tactics.Failure "intro pattern not applicable")

  | `Hyp id, Args.SAndOr ao_ip ->
    do_and_or_pat id ao_ip s

(*------------------------------------------------------------------*)
(** [do_intro name t judge] introduces the topmost connective
    of the conclusion formula. *)
let rec do_intro (s : TraceSequent.t) : Args.ip_handler * sequent =
  match TraceSequent.conclusion s with
  | ForAll ((Vars.EVar x) :: vs,f) ->
    let x' = Vars.make_new_from x in

    let subst = [Term.ESubst (Term.Var x, Term.Var x')] in

    let f = match vs with
      | [] -> f
      | _ -> ForAll (vs,f) in

    let new_formula = Term.subst subst f in
    ( `Var (Vars.EVar x'),
      TraceSequent.set_conclusion new_formula s )

  | ForAll ([],f) ->
    (* FIXME: this case should never happen. *)
    do_intro (TraceSequent.set_conclusion f s)

  | Impl(lhs,rhs)->
    let id, s = Hyps.add_i Args.Unnamed lhs s in
    let s = TraceSequent.set_conclusion rhs s in
    ( `Hyp id, s )

  | Not f ->
    let id, s = Hyps.add_i Args.Unnamed f s in
    let s = TraceSequent.set_conclusion False s in
    ( `Hyp id, s )

  | Atom (`Message (`Neq,u,v)) ->
    let h = `Message (`Eq,u,v) in
    let id, s = Hyps.add_i Args.Unnamed (Atom h) s in 
    let s = TraceSequent.set_conclusion False s in
    ( `Hyp id, s )

  | _ -> soft_failure Tactics.NothingToIntroduce

let do_intro_pat (ip : Args.simpl_pat) s : sequent list =
  let handler, s = do_intro s in
  do_simpl_pat handler ip s

(** Correponds to `intro *`, to use in automated tactics. *)
let rec intro_all (s : TraceSequent.t) : TraceSequent.t list =
  try
    let s_ip = Args.(SNamed AnyName) in
    let ss = do_intro_pat s_ip s in
    List.concat_map intro_all ss
      
  with Tactics.Tactic_soft_failure (_,NothingToIntroduce) -> [s]

(*------------------------------------------------------------------*)
let do_destruct hid s =
  (* Only destruct the top-most connective *)
  let handlers, s = do_and_pat hid 2 s in
  [List.fold_left (fun s handler ->
       (* TODO: location errors *)
       do_naming_pat handler Args.AnyName s
     ) s handlers]

let destruct_tac args s sk fk =
  try match args with
    | [Args.String_name h; Args.AndOrPat pat] ->
      let hid, _ = Hyps.by_name h s in
      sk (do_and_or_pat hid pat s) fk

    | [Args.String_name h] ->
      let hid, _ = Hyps.by_name h s in
      sk (do_destruct hid s) fk

    | _ -> Tactics.(hard_failure (Failure "improper arguments"))
  with Tactics.Tactic_soft_failure (_,e) -> fk e

let () =
  T.register_general "destruct"
    ~tactic_help:{general_help = "Destruct an hypothesis. An optional And/Or \
                                  introduction pattern can be given.\n\n\
                                  Usages: destruct H.\n\
                                 \        destruct H as [A | [B C]]";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    destruct_tac


(*------------------------------------------------------------------*)
(** Quantifiers *)

(** [goal_exists_intro judge ths] introduces the existentially
    quantified variables in the conclusion of the judgment,
    using [ths] as existential witnesses. *)
let goal_exists_intro  ths (s : TraceSequent.t) =
  match TraceSequent.conclusion s with
  | Exists (vs,f) when List.length ths = List.length vs ->
    let table = TraceSequent.table s in
    let nu = Theory.parse_subst table (TraceSequent.env s) vs ths in
    let new_formula = Term.subst nu f in 
    [TraceSequent.set_conclusion new_formula s]
  | _ ->
      soft_failure (Tactics.Failure "cannot introduce exists")

(* Does not rely on the typed register, as it parses a subt. *)
let () =
  T.register_general "exists"
    ~tactic_help:{general_help = "Introduce the existentially quantified \
                                  variables in the conclusion of the judgment, \
                                  using the arguments as existential witnesses.\
                                  \n\nUsage: exists v1, v2, ...";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    (fun l s sk fk ->
       let ths =
         List.map
           (function
              | Args.Theory tm -> tm
              | _ -> Tactics.(hard_failure (Failure "improper arguments")))
           l
       in
         match goal_exists_intro ths s with
           | subgoals -> sk subgoals fk
           | exception Tactics.Tactic_soft_failure (_,e) -> fk e)


(*------------------------------------------------------------------*)

let rec simpl_left s =
  let func _ f = match f with
    | Term.False | Term.And _ | Term.Exists _ -> true
    | _ -> false in
    
  match Hyps.find_opt func s with
  | None -> Some s
  | Some (id,f) -> 
    match f with
    | False -> None
    | And (f,g) ->
      let s = Hyps.remove id s in
      simpl_left (Hyps.add_list [(Args.AnyName, f); (Args.AnyName, g)] s)

    | Exists (vs,f) ->
      let s = Hyps.remove id s in
      let env = ref @@ TraceSequent.env s in
      let subst =
        List.map
          (fun (Vars.EVar v) ->
             Term.ESubst  (Term.Var v,
                           Term.Var (Vars.make_fresh_from_and_update env v)))
          vs
      in
      let f = Term.subst subst f in
      simpl_left (Hyps.add Args.AnyName f (TraceSequent.set_env !env s))

    | _ -> assert false

let simpl_left_tac s = match simpl_left s with
  | None -> []
  | Some s -> [s]

let () =
  T.register "simpl_left"
    ~tactic_help:{general_help = "Introduce all conjunctions, existentials and \
                                  false hypotheses.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    simpl_left_tac

(*------------------------------------------------------------------*)
(** Generalize *)

let generalize ~loc (v : Vars.evar) s : sequent =
  let env = TraceSequent.env s in
  if not (List.mem v (Vars.to_list env)) then
    hard_failure (Failure (Fmt.str "unknown variable %a" Vars.pp_e v));

  let bad_hyps = Hyps.fold (fun id f bad_hyps -> 
      if Vars.Sv.mem v (Term.fv f) 
      then id :: bad_hyps
      else bad_hyps
    ) s [] in
  
  if bad_hyps <> [] then
    soft_failure (Failure (Fmt.str "%a appears in hypotheses %a" 
                             Vars.pp_e v (Fmt.list Ident.pp) bad_hyps));

  let goal = Term.mk_forall [v] (TraceSequent.conclusion s) in
  let env = Vars.rm_evar env v in
 
  TraceSequent.set_conclusion goal s
  |> TraceSequent.set_env env


let generalize_tac (args : Args.parser_arg list) s sk fk = 
  try
    let s = 
      List.fold_left (fun s arg -> 
          let tbl, env = TraceSequent.table s, TraceSequent.env s in
          match Args.convert_args tbl env [arg] (Args.Sort Args.ETerm) with
          | Args.Arg (Args.ETerm (_, Term.Var v, loc)) ->
            generalize ~loc (Vars.EVar v) s

          | Args.Arg (Args.ETerm (_, _, loc)) ->
            hard_failure ~loc (Failure "arguments must be variables")

          | _ -> hard_failure (Failure "improper arguments")
        ) s args in
    sk [s] fk
  with Tactics.Tactic_soft_failure (_,e) -> fk e
      
let () =
  T.register_general "generalize"
    ~tactic_help:{
      general_help = "Generalize over some variables";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    generalize_tac
  

(*------------------------------------------------------------------*)
(** Induction *)

let induction s  =
  match TraceSequent.conclusion s with
  | ForAll ((Vars.EVar v)::vs,f) ->
    (match Vars.sort v with
       Sorts.Timestamp ->
       (
         (* We need two fresh variables in env,
          * but one will not be kept in the final environment. *)
         let env,v' = Vars.make_fresh_from (TraceSequent.env s) v in
         let _,v'' = Vars.make_fresh_from env v in
         (* Introduce v as v'. *)
         let f' = match vs with
           | [] -> f
           | _ -> ForAll (vs,f) in
         let f' = Term.subst [Term.ESubst (Term.Var v,Term.Var v')] f' in
         (* Use v'' to form induction hypothesis. *)
         let (-->) a b = Impl (a,b) in
         let ih =
           ForAll ((Vars.EVar v'')::vs,
                   (Atom (`Timestamp (`Lt,Term.Var v'',Term.Var v)
                            :> generic_atom) -->
                    Term.subst
                      [Term.ESubst (Term.Var v,Term.Var v'')] f)) in

         let goal = Term.mk_impl ih f' in

         let s = s |> TraceSequent.set_env env
                   |> TraceSequent.set_conclusion goal in
         [s]
       )
     | _ ->
       Tactics.soft_failure 
         (Tactics.Failure
            "conclusion must be an universal quantification over a timestamp")
    )
  | _ ->
    Tactics.soft_failure 
      (Tactics.Failure "Conclusion must be an \
                        universal quantification over a timestamp")

let () = T.register "induction"
     ~tactic_help:{general_help = "Apply the induction scheme to the conclusion.";
                   detailed_help = "If the conclusion is a `ForAll ts. phi`, \
                                    where ts does not occur in the hypothesis, \
                                    creates a sub goal where ts is init, and \
                                    another where we assume as hypothesis phi \
                                    over pred(ts).";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
     induction

(*------------------------------------------------------------------*)
(** [assumption judge sk fk] proves the sequent using the axiom rule. *)
let assumption (s : TraceSequent.t) =
  let goal = TraceSequent.conclusion s in
  if goal = Term.True || Hyps.is_hyp goal s || Hyps.is_hyp False s then
    let () = dbg "assumption %a" Term.pp goal in
    []
  else soft_failure Tactics.NotHypothesis

let () = T.register "assumption"
    ~tactic_help:{
      general_help = "Search for the conclusion inside the hypothesis.";
      detailed_help = "";
      usages_sorts = [Sort None];
      tactic_group = Logical }
    assumption

(*------------------------------------------------------------------*)
let is_hyp_or_lemma name s =
  Hyps.mem_name (L.unloc name) s || Prover.is_goal_formula name

(** Get a hypothesis or lemma by name (in the hyp case, return its id). *)
let get_hyp_or_lemma name s =
  let hyp_opt, (f,system) =
    if Hyps.mem_name (L.unloc name) s then
      let id, f = Hyps.by_name name s in
      Some id, (f, TraceSequent.system s)
    else None, Prover.get_goal_formula name in

  (* Verify that it applies to the current system. *)
  begin
    match TraceSequent.system s, system with
    | s1, s2 when s1 = s2 -> ()
    | Single (Left s1),  SystemExpr.SimplePair s2 when s1 = s2 -> ()
    | Single (Right s1), SystemExpr.SimplePair s2 when s1 = s2 -> ()
    | _ -> hard_failure Tactics.NoAssumpSystem
  end ;
  hyp_opt, f

(*------------------------------------------------------------------*)
(** [use ip name ths judge] applies the formula named [gp],
  * eliminating its universally quantified variables using [ths],
  * and eliminating implications (and negations) underneath.
  * If given an introduction patterns, apply it to the generated hypothesis. *)
let use ip (name : lsymb) (ths:Theory.term list) (s : TraceSequent.t) =
  (* Get formula to apply. *)
  let _, f = get_hyp_or_lemma name s in

  (* Get universally quantifier variables, verify that lengths match. *)
  let uvars,f = match f with
    | ForAll (uvars,f) -> uvars,f
    | _ -> [],f in

  if List.length uvars <> List.length ths then
    Tactics.(soft_failure (Failure "incorrect number of arguments")) ;

  let subst =
    let table = TraceSequent.table s in
    Theory.parse_subst table (TraceSequent.env s) uvars ths in

  (* Formula with universal quantifications introduced. *)
  let f = Term.subst subst f in

  (* Compute subgoals by introducing implications on the left. *)
  let rec aux subgoals = function
    | Term.Impl (h,c) ->
        let s' = TraceSequent.set_conclusion h s in
        aux (s'::subgoals) c
    | Term.Not h ->
        let s' = TraceSequent.set_conclusion h s in
        List.rev (s'::subgoals)
    | f ->
      let idf, s0 = Hyps.add_i Args.AnyName f s in
      let s0 = match ip with
        | None -> [s0]
        | Some ip -> do_simpl_pat (`Hyp idf) ip s0 in
      s0 @ List.rev subgoals
  in

  aux [] f

(* we use tac_apply for both `use` tactic. *)
let tac_apply args s sk fk =
  let ip, args = match args with
    | Args.SimplPat ip :: args -> Some ip, args
    | args                     -> None, args in
  match args with
  | Args.String_name id :: th_terms ->
    let th_terms =
      List.map
        (function
          | Args.Theory th -> th
          | _ -> hard_failure
                   (Tactics.Failure "improper arguments"))
        th_terms
    in
    begin match use ip id th_terms s with
      | subgoals -> sk subgoals fk
      | exception Tactics.Tactic_soft_failure (_,e) -> fk e
    end
  | _ -> Tactics.(hard_failure (Failure "improper arguments"))


let tac_apply args s sk fk =
  try tac_apply args s sk fk with
  | Tactics.Tactic_soft_failure (_,e) -> fk e

(* Does not rely on the typed register as it parses a subst *)
let () =
  T.register_general "use"
    ~tactic_help:{general_help = "Apply an hypothesis with its universally \
                                  quantified variables instantiated with the \
                                  arguments.\n\n\
                                  Usages: use H with v1, v2, ...\n\
                                 \        use H with ... as ...";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    tac_apply

(*------------------------------------------------------------------*)
(** [tac_assert f j sk fk] generates two subgoals, one where [f] needs
  * to be proved, and the other where [f] is assumed. *)
let tac_assert (args : Args.parser_arg list) s sk fk =
  try
    let env, tbl = TraceSequent.env s, TraceSequent.table s in
    let ip, f = match args with
      | [f] -> None, f
      | [f; Args.SimplPat ip] -> Some ip, f
      | _ -> Tactics.(hard_failure (Failure "improper argument")) in

    let f = match Args.convert_args tbl env [f] Args.(Sort Boolean) with
      | Args.(Arg (Boolean f)) -> f
      | _ -> Tactics.(hard_failure (Failure "improper argument")) in

    let s1 = TraceSequent.set_conclusion f s in
    let id, s2 = Hyps.add_i Args.AnyName f s in
    let s2 = match ip with
      | Some ip -> do_simpl_pat (`Hyp id) ip s2
      | None -> [s2] in
    sk (s1 :: s2) fk

  with Tactics.Tactic_soft_failure (_,e) -> fk e

let () =
  T.register_general "assert"
    ~tactic_help:{general_help = "Add an assumption to the set of hypothesis, \
                                  and produce the goal for\
                                  \nthe proof of the assumption.\n\
                                  Usages: assert f.\n \
                                 \       assert f as intro_pat";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    tac_assert


(*------------------------------------------------------------------*)
(** {2 Structural Tactics} *)

let happens_premise (s : sequent) (a : Term.timestamp) =
  TraceSequent.set_conclusion (Term.Atom (`Happens a)) s

(*------------------------------------------------------------------*)
let depends Args.(Pair (Timestamp a1, Timestamp a2)) s =
  match a1, a2 with
  | Term.Action(n1, is1), Term.Action (n2, is2) ->
    let table = TraceSequent.table s in    
    if Action.(depends (of_term n1 is1 table) (of_term n2 is2 table)) then
        let atom = (Atom (`Timestamp (`Lt,a1,a2))) in       
        let g = Term.mk_impl atom (TraceSequent.conclusion s) in
        [happens_premise s a2; 
         TraceSequent.set_conclusion g s]
    else
      soft_failure
        (Tactics.NotDepends (Fmt.strf "%a" Term.pp a1,
                             Fmt.strf "%a" Term.pp a2))
  | _ -> soft_failure (Tactics.Failure "arguments must be actions")

let () =
  T.register_typed "depends"
    ~general_help:"If the second action depends on the first \
                   action, and if the second \
                   action happened, \
                   add the corresponding timestamp inequality."
    ~detailed_help:"Whenever action A1[i] must happen before A2[i], if A2[i] \
                    occurs in the trace, we can add A1[i]. "
    ~tactic_group:Structural
    depends Args.(Pair (Timestamp, Timestamp))


(*------------------------------------------------------------------*)
(** {2 Rewriting types and functions}*)

type rw_target = [`Goal | `Hyp of Ident.t]

let target_all s : rw_target list =
  `Goal :: List.map (fun ldecl -> `Hyp (fst ldecl)) (Hyps.to_list s)

(** A rewrite rule is a tuple: 
    (universally quantified variables, premisses, left term, right term)
    Invariant: if (sv,??,l,r) is a rewrite rule, then
    - sv ??? FV(l)
    - ((FV(r) ??? FV(??)) ??? sv) ??? FV(l) *)
type 'a rw_rule =  (Vars.Sv.t * Term.formula list * 'a term * 'a term)

type rw_erule = (Vars.Sv.t * Term.formula list * Term.esubst)

type rw_arg = 
  | Rw_rw of Ident.t option * rw_erule
  (* The ident is the ident of the hyp the rule came from (if any) *)
             
  | Rw_expand of Theory.term

type rw_earg = Args.rw_count * rw_arg

(** Check that the rule is correct. *)
let check_rule ((sv, h, l, r) : 'a rw_rule) : bool =
  let fvl, fvr = Term.fv l, Term.fv r in
  let sh = List.fold_left (fun sh h ->
      Vars.Sv.union sh (Term.fv h)
    ) Vars.Sv.empty h
  in
  Vars.Sv.subset sv fvl && 
  Vars.Sv.subset (Vars.Sv.inter (Vars.Sv.union fvr sh) sv) fvl

let check_erule ((sv, h, Term.ESubst (l,r)) : rw_erule) : bool =
  check_rule (sv, h, l, r)

(* rewrite in a single target *)
let do_target 
    (doit : (Term.formula * Ident.t option) -> Term.formula * Term.formula list) 
    (s : sequent) (t : rw_target) : sequent * sequent list =
  let f, s, tgt_id = match t with
    | `Goal -> TraceSequent.conclusion s, s, None
    | `Hyp id -> Hyps.by_id id s, Hyps.remove id s, Some id
  in

  let f,subs = doit (f,tgt_id) in
  let subs : sequent list = 
    List.map (fun sub -> TraceSequent.set_conclusion sub s) subs
  in

  match t with
  | `Goal -> TraceSequent.set_conclusion f s, subs
  | `Hyp id -> Hyps.add (Args.Named (Ident.name id)) f s, subs

let do_targets doit (s : sequent) targets : sequent * sequent list = 
  let s, subs = 
    List.fold_left (fun (s,subs) target ->
        let s, subs' = do_target doit s target in
        s, (List.rev subs') @ subs
      ) (s,[]) targets
  in
  s, List.rev subs
    

(*------------------------------------------------------------------*)
let unfold_macro t (s : sequent) =
  match t with
    | Macro ((mn, sort, is),l,a) ->
      if not (TraceSequent.query_happens ~precise:true s a) then
        soft_failure (Tactics.MustHappen a);
      
      let mdef = Macros.get_definition (mk_trace_cntxt s) sort mn is a in

      [Term.ESubst (Macro ((mn, sort, is),l,a), mdef)]
      
    | _ -> 
      soft_failure (Tactics.Failure "can only expand macros")

let unfold_macro ~canfail t s : Term.esubst list =
  try unfold_macro t s with
  | Tactics.Tactic_soft_failure _ when not canfail -> []


let expand_macro (targets : rw_target list) t (s : sequent) : sequent =
  let subst = unfold_macro ~canfail:true t s in
  if subst = [] then soft_failure (Failure "nothing to expand");

  let doit (f,_) = Term.subst subst f, [] in
  let s, subs = do_targets doit s targets in
  assert (subs = []);
  s
     

let find_occs_macro
  : type a. Symbols.macro Symbols.t -> ?st:Term.St.t -> a term -> Term.St.t =
  fun m ?st t -> 
  let rec find st (ETerm t) = 
    let st = match t with
      | Macro ((m',_,_), _, _) when m' = m -> Term.St.add (Term.ETerm t) st
      | _ -> st in
    Term.tfold (fun t st -> find st t) t st
  in
  find (Utils.odflt Term.St.empty st) (ETerm t)
      
let expand (targets : rw_target list) (arg : Theory.term) s = 
  let tbl = TraceSequent.table s in
  match Args.convert_as_lsymb [Args.Theory arg] with
  | Some m ->
    let m = Symbols.Macro.of_lsymb m tbl in
    let occs = 
      List.fold_left (fun occs target -> match target with
          | `Goal -> 
            find_occs_macro m ~st:occs (TraceSequent.conclusion s) 
          | `Hyp id ->
            let f = Hyps.by_id id s in
            find_occs_macro m ~st:occs f
        ) St.empty targets
    in
    let subst = 
      Term.St.fold (fun (ETerm t) subst -> 
          unfold_macro ~canfail:false t s @ subst
        ) occs [] in
    
    if subst = [] then soft_failure (Failure "nothing to expand");

    let doit (f,_) = Term.subst subst f, [] in
    let s, subs = do_targets doit s targets in
    assert (subs = []);
    s

  | _ ->
    let env = TraceSequent.env s in
    match Args.convert_args tbl env [Args.Theory arg] Args.(Sort ETerm) with
    | Args.Arg (Args.ETerm (Sorts.Boolean, f, loc)) ->
      expand_macro targets f s
        
    | Args.Arg (Args.ETerm (Sorts.Message, f, loc)) ->
      expand_macro targets f s
        
    | _ ->
      hard_failure (Tactics.Failure "expected a message or boolean term")

let expands args s =
  List.fold_left (fun s arg -> expand (target_all s) arg s) s args 

let expand_tac args s sk fk =
  try 
    let args = List.map (function
        | Args.Theory t -> t
        | _ -> hard_failure (Failure "improper arguments")
      ) args
    in
    sk [expands args s] fk
  with Tactics.Tactic_soft_failure (_,e) -> fk e


let () = T.register_general "expand"
    ~tactic_help:{
      general_help  = "Expand all occurences of the given macro inside the \
                       goal.";
      detailed_help = "Can only be called over macros with fully defined \
                       timestamps.";
      tactic_group  = Structural;
      usages_sorts  = [Sort Args.String; Sort Args.Message; Sort Args.Boolean]; }
    expand_tac

(*------------------------------------------------------------------*)
(** [congruence judge sk fk] try to close the goal using congruence, else
    calls [fk] *)
let congruence (s : TraceSequent.t) : bool Utils.timeout_r =
  match simpl_left s with
  | None -> Utils.Result true
  | Some s ->
    let conclusions =
      Utils.odflt [] (Term.disjunction_to_literals (TraceSequent.conclusion s)) 
    in

    let term_conclusions =
      List.fold_left (fun acc conc -> match conc with
          | `Pos, (#generic_atom as at) ->
            let at = (at :> Term.generic_atom) in
            Term.(Not (Atom at)) :: acc
          | `Neg, (#generic_atom as at) ->
            Term.Atom at :: acc)
        []
        conclusions
    in
    let s = List.fold_left (fun s f ->
        Hyps.add Args.AnyName f s
      ) s term_conclusions
    in
    TraceSequent.eq_atoms_valid s

(** [constraints s] proves the sequent using its trace formulas. *)
let congruence_tac (s : TraceSequent.t) =
  match Tactics.timeout_get (congruence s) with 
  | true ->
    let () = dbg "closed by congruence" in
    []

  | false -> 
    let () = dbg "congruence failed" in
    soft_failure Tactics.CongrFail

let () = T.register "congruence"
    ~tactic_help:
      {general_help = "Tries to derive false from the messages equalities.";
       detailed_help = "It relies on the reflexivity, transitivity \
                        and stability by function application \
                        (f(u)=f(v) <=> u=v).";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    congruence_tac

(*------------------------------------------------------------------*)
let constraints (s : TraceSequent.t) =
  match simpl_left s with
  | None -> Utils.Result true
  | Some s ->
    let conclusions =
      Utils.odflt [] (Term.disjunction_to_literals (TraceSequent.conclusion s)) 
    in
    let trace_conclusions =
      List.fold_left (fun acc conc -> match conc with
          | `Pos, (#trace_atom as at) ->
            let at = (at :> Term.generic_atom) in
            Term.(Not (Atom at)) :: acc
          | `Neg, (#trace_atom as at) ->
            Term.Atom at :: acc
          | _ -> acc)
        []
        conclusions
    in
    let s = List.fold_left (fun s f ->
        Hyps.add Args.AnyName f s
      ) s trace_conclusions
    in
    TraceSequent.constraints_valid s

(** [constraints s] proves the sequent using its trace formulas. *)
let constraints_tac (s : TraceSequent.t) =
  match Tactics.timeout_get (constraints s) with 
  | true ->
    let () = dbg "closed by constraints" in
    []
  | false -> soft_failure (Tactics.Failure "constraints satisfiable")

let () = T.register "constraints"
    ~tactic_help:
      {general_help = "Tries to derive false from the trace formulas.";
       detailed_help = "From ordering constraints on the timestamps, \
                        checks that we can build an acyclic graph on \
                        them, i.e., if they are a possible trace.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    constraints_tac



(*------------------------------------------------------------------*)
(** Length *)

let namelength Args.(Pair (Message n, Message m)) s =
  match n, m with
  | Name n, Name m ->
    let f = Term.(Atom (`Message (`Eq,
                                  Fun (f_len,[Name n]),
                                  Fun (f_len,[Name m])))) in

    (* let id = Hyps.fresh_id ~approx:true "HL" s in
     * [Hyps.add_formula id f s] *)
    [TraceSequent.set_conclusion
       (Term.mk_impl f (TraceSequent.conclusion s)) s]

  | _ -> Tactics.(soft_failure (Failure "expected names"))

let () =
  T.register_typed "namelength"
    ~general_help:"Adds the fact that two names have the same length."
    ~detailed_help:""
    ~tactic_group:Structural
    namelength Args.(Pair (Message, Message))

(*------------------------------------------------------------------*)
(** Eq-Indep Axioms *)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

(** Add index constraints resulting from names equalities, modulo the TRS.
    The judgment must have been completed before calling [eq_names]. *)
let eq_names (s : TraceSequent.t) =
  let trs = get_trs s in
  let terms = TraceSequent.get_all_messages s in
  (* we start by collecting equalities between names implied by the indep axiom.
  *)
  let new_eqs = Completion.name_indep_cnstrs trs terms in
  let s =
    List.fold_left (fun s c ->
        let () = dbg "new name equality (indep): %a" Term.pp c in
        Hyps.add Args.AnyName c s
      ) s new_eqs in

  (* we now collect equalities between timestamp implied by equalities between
     names. *)
  let trs = get_trs s in
  let cnstrs = 
    Completion.name_index_cnstrs trs (TraceSequent.get_all_messages s)
  in
  let s =
    List.fold_left (fun s c ->
        let () = dbg "new index equality (names): %a" Term.pp c in
        Hyps.add Args.AnyName c s
      ) s cnstrs
  in
  [s]

let () = T.register "eqnames"
    ~tactic_help:
      {general_help = "Add index constraints resulting from names equalities, \
                       modulo the known equalities.";
       detailed_help = "If n[i] = n[j] then i = j. \
                        This is checked on all name equality entailed \
                        by the current context.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    eq_names

(*------------------------------------------------------------------*)
(** Add terms constraints resulting from timestamp and index equalities. *)
let eq_trace (s : TraceSequent.t) =
  let ts_classes = 
    Tactics.timeout_get (TraceSequent.get_ts_equalities ~precise:false s) 
  in
  let ts_classes = List.map (List.sort_uniq Stdlib.compare) ts_classes in
  let ts_subst =
    let rec asubst e = function
        [] -> []
      | p::q -> Term.ESubst (p,e) :: (asubst e q)
    in
    List.map (function [] -> [] | p::q -> asubst p q) ts_classes
    |> List.flatten
  in
  let ind_classes = 
    Tactics.timeout_get (TraceSequent.get_ind_equalities ~precise:false s) 
  in
  let ind_classes = List.map (List.sort_uniq Stdlib.compare) ind_classes in
  let ind_subst =
    let rec asubst e = function
        [] -> []
      | p::q -> Term.ESubst (Term.Var p,Term.Var e) :: (asubst e q)
    in
    (List.map (function [] -> [] | p::q -> asubst p q) ind_classes)
    |> List.flatten
  in
  let terms = TraceSequent.get_all_messages s in
  let facts =
    List.fold_left
      (fun acc t ->
         let normt : Term.message = Term.subst (ts_subst @ ind_subst) t in
         if normt = t then
           acc
         else
           Term.Atom (`Message (`Eq, t, normt)) ::acc)
      [] terms
  in
  let s =
    List.fold_left (fun s c ->
        let () = dbg "new trace equality: %a" Term.pp c in
        Hyps.add Args.AnyName c s
      ) s facts
  in
  [s]

let () = T.register "eqtrace"
    ~tactic_help:
      {general_help = "Add terms constraints resulting from timestamp \
                       and index equalities.";
       detailed_help = "Whenver i=j or ts=ts', we can substitute one \
                        by another in the other terms.";
       usages_sorts = [Sort None];
       tactic_group = Structural}
    eq_trace

(*------------------------------------------------------------------*)
let fresh_param m1 m2 = match m1,m2 with
  | Name (n,is), _ -> (n,is,m2)
  | _, Name (n,is) -> (n,is,m1)
  | _ ->
    soft_failure
      (Tactics.Failure "can only be applied on hypothesis of the form \
                        t=n or n=t")

(* Direct cases - names appearing in the term [t] *)
let mk_fresh_direct (cntxt : Constr.trace_cntxt) env n is t =
  (* iterate over [t] to search subterms of [t] equal to a name *)
  let list_of_indices =
    let iter = new Fresh.get_name_indices ~cntxt false n in
    iter#visit_message t ;
    iter#get_indices
  in
  (* build the formula expressing that there exists a name subterm of [t]
   * equal to the name ([n],[is]) *)
  let mk_case (js : Sorts.index Vars.var list) =
    (* select bound variables *)
    let bv = List.filter (fun i -> not (Vars.mem env (Vars.name i))) js in

    let env_local = ref env in
    let bv' = List.map (Vars.make_fresh_from_and_update env_local) bv in

    let subst =
      List.map2
        (fun i i' -> ESubst (Term.Var i, Term.Var i'))
        bv bv'
    in

    let js = List.map (Term.subst_var subst) js in

    Term.mk_exists
      (List.map (fun i -> Vars.EVar i) bv')
      (Term.mk_indices_eq is js)
  in

  let cases = List.map mk_case list_of_indices in
  Term.mk_ors (List.sort_uniq Stdlib.compare cases)

(* Indirect cases - names ([n],[is']) appearing in actions of the system *)
let mk_fresh_indirect (cntxt : Constr.trace_cntxt) env n is t =
  let list_of_actions_from_term =
    let iter = new Fresh.get_actions ~cntxt false in
    iter#visit_message t ;
    iter#get_actions in

  let tbl_of_action_indices = ref [] in

  let () = SystemExpr.(iter_descrs cntxt.table cntxt.system
    (fun action_descr ->
      let iter = new Fresh.get_name_indices ~cntxt true n in
      iter#visit_formula (snd action_descr.condition) ;
      iter#visit_message (snd action_descr.output) ;
      List.iter (fun (_,t) -> iter#visit_message t) action_descr.updates;
      (* we add only actions in which name [n] occurs *)
      let action_indices = iter#get_indices in
      if List.length action_indices > 0 then
        tbl_of_action_indices :=
          (action_descr, action_indices)
          :: !tbl_of_action_indices))
  in

  (* the one case occuring in [a] with indices [is_a].'
     For n[is] to be equal to n[is_a], we must have is=is_a.
     Hence we substitute is_a by is. *)
  let mk_case a is_a =
    let env_local = ref env in

    (* We only quantify over indices that are not in is_a *)
    let eindices =
      List.filter (fun v -> not (List.mem v is_a)) a.Action.indices in

    let eindices' =
      List.map (Vars.make_fresh_from_and_update env_local) eindices in

    (* refresh existantially quant. indices, and subst is_a by is. *)
    let subst =
      List.map2
        (fun i i' -> ESubst (Term.Var i, Term.Var i'))
        (eindices @ is_a) (eindices' @ is)
    in

    (* we apply [subst] to the action [a] *)
    let new_action =
      SystemExpr.action_to_term cntxt.table cntxt.system
        (Action.subst_action subst a.Action.action) in

    let timestamp_inequalities =
      Term.mk_ors
        (List.sort_uniq Stdlib.compare
           (List.map
              (fun (action_from_term,strict) ->
                 if strict
                 (* [strict] is true if [action_from_term] refers to
                    an input *)
                 then Term.Atom (`Timestamp (`Lt,
                                             new_action,
                                             action_from_term))
                 else Term.Atom (Term.mk_timestamp_leq
                                   new_action
                                   action_from_term))
              list_of_actions_from_term))
    in

    (* Remark that the equations below are not redundant.
       Indeed, assume is = (i,j) and is_a = (i',i').
       Then, the substitution [subst] will map i' to i
       (the second substitution i->j is shadowed)
       But, by substituting in the vector of equalities, we correctly retrieve
       that i = j. *)
    let idx_eqs =
      Term.mk_indices_eq is (List.map (Term.subst_var subst) is_a)
    in

    Term.mk_exists
      (List.map (fun i -> Vars.EVar i) eindices')
      (Term.mk_and
         timestamp_inequalities
         idx_eqs)
  in

  (* Do all cases of action [a] *)
  let mk_cases_descr (a, indices_a) =
    List.map (mk_case a) indices_a in

  let cases = List.map mk_cases_descr !tbl_of_action_indices
              |> List.flatten in

  mk_ors cases


let fresh (Args.String m) s =
  try
    let id,hyp = Hyps.by_name m s in
    begin match hyp with
      | Atom (`Message (`Eq,m1,m2)) ->
        let (n,is,t) = fresh_param m1 m2 in
        let env   = TraceSequent.env s in
        let cntxt = mk_trace_cntxt s in
        let phi_direct = mk_fresh_direct cntxt env n is t in
        let phi_indirect = mk_fresh_indirect cntxt env n is t in
        let phi = Term.mk_or phi_direct phi_indirect in

        let goal = Term.mk_impl phi (TraceSequent.conclusion s) in
        [TraceSequent.set_conclusion goal s]
        (* all_left_introductions s [new_hyp,""] *)

      | _ -> soft_failure
               (Tactics.Failure "can only be applied on message hypothesis")
    end
  with
  | Fresh.Var_found ->
    soft_failure
      (Tactics.Failure "can only be applied on ground terms")

let () =
  T.register_typed "fresh"
    ~general_help:"Given a message equality M of the form t=n, \
                   add an hypothesis expressing that n is a subterm of t."
    ~detailed_help:"This condition checks that all occurences of the same name \
                    in other actions cannot have happened before this action."
    ~tactic_group:Structural
    fresh Args.String

(*------------------------------------------------------------------*)
let apply_substitute subst s =
    let s =
    match subst with
      | Term.ESubst (Term.Var v, t) :: _ when
        not (List.mem (Vars.EVar v) (Term.get_vars t)) ->
          TraceSequent.set_env (Vars.rm_var (TraceSequent.env s) v) s
      | _ -> s
  in
  [TraceSequent.subst subst s]

let substitute_mess (m1, m2) s =
  let subst =
        let trs = get_trs s in
        if Completion.check_equalities trs [Term.ESubst (m1,m2)] then
          [Term.ESubst (m1,m2)]
        else
          soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_ts (ts1, ts2) s =
  let subst =
      let models = get_models s in
      if Constr.query ~precise:true models [(`Pos, `Timestamp (`Eq,ts1,ts2))] then
        [Term.ESubst (ts1,ts2)]
      else
        soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_idx (i1 , i2 : Sorts.index Term.term * Sorts.index Term.term) s =
  let i1, i2 =  match i1, i2 with
    | Var i1, Var i2 -> i1, i2
    | (Diff _ | Macro _), _
    | _, (Macro _ | Diff _) ->
      hard_failure
        (Tactics.Failure "only variables are supported when substituting \
                          index terms")
  in

  let subst =
    let models = get_models s in
    if Constr.query ~precise:true models [(`Pos, `Index (`Eq,i1,i2))] then
      [Term.ESubst (Term.Var i1,Term.Var i2)]
    else
      soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_tac arg s =
  let open Args in
  match arg with
  | Pair (ETerm (Sorts.Message, f1, _), ETerm (Sorts.Message, f2, _)) ->
    substitute_mess (f1,f2) s

  | Pair (ETerm (Sorts.Timestamp, f1, _), ETerm (Sorts.Timestamp, f2, _)) ->
    substitute_ts (f1,f2) s

  | Pair (ETerm (Sorts.Index, f1, _), ETerm (Sorts.Index, f2, _)) ->
    substitute_idx (f1,f2) s

  | _ ->
    hard_failure
      (Tactics.Failure "expected a pair of messages, booleans or a pair of \
                        index variables")

let () =
  T.register_typed "subst"
    ~general_help:"If i = t where i is a variable, substitute all occurences \
                   of i by t and remove i from the context variables."
    ~detailed_help:""
    ~tactic_group:Structural
    ~usages_sorts:[Args.(Sort (Pair (Index, Index)));
                   Args.(Sort (Pair (Timestamp, Timestamp)));
                   Args.(Sort (Pair (Message, Message)))]
    substitute_tac Args.(Pair (ETerm, ETerm))



(*------------------------------------------------------------------*)
let autosubst s =
  let id, f = match
      Hyps.find_map
        (fun id f -> match f with
           | Atom (`Timestamp (`Eq, Term.Var x, Term.Var y) as atom) ->
             Some (id, atom)
           | Atom (`Index (`Eq, x, y) as atom) ->
             Some (id,atom)
           | _ -> None)
        s
    with | Some (id,f) -> id, f
         | None -> Tactics.(soft_failure (Failure "no equality found"))
  in
  let s = Hyps.remove id s in

  let process : type a. a Vars.var -> a Vars.var -> TraceSequent.t =
    fun x y ->

      (* Just remove the equality if x and y are the same variable. *)
      if x = y then s else
      (* Otherwise substitute the newest variable by the oldest one,
       * and remove it from the environment. *)
      let x,y =
        if Vars.compare x y <= 0 then y,x else x,y
      in

      let () = dbg "subst %a by %a" Vars.pp x Vars.pp y in

      let s =
        TraceSequent.set_env (Vars.rm_var (TraceSequent.env s) x) s
      in
        TraceSequent.subst [Term.ESubst (Term.Var x, Term.Var y)] s
  in
    match f with
    | `Timestamp (`Eq, Term.Var x, Term.Var y) -> [process x y]
    | `Index (`Eq, x, y)                       -> [process x y]
    | _ -> assert false

(* (*------------------------------------------------------------------*)
 * (** Expects a list of theory elements of the form cond@T :: formula :: l and
 *      output@T :: message :: l, and produces from it the corresponding
 *      substitution over Action.descrs. *)
 * let parse_substd table tsubst s =
 *   let failure () = Tactics.(soft_failure (Failure "ill-typed substitution")) in
 *   let conv_env = Theory.{ table = table; cntxt = InGoal; } in
 * 
 *   let rec parse_substd0 s =
 *     match s with
 *     | [] -> []
 *     | [a] -> Tactics.(soft_failure (Failure "ill-typed substitution"))
 *     | (Args.Theory mterm)::(Args.Theory b)::q ->
 *       begin
 *         match Theory.convert conv_env tsubst mterm Sorts.Boolean,
 *               Theory.convert conv_env tsubst b Sorts.Boolean with
 *         | Term.Macro ((mn, sort, is),l,a), ncond ->
 *           begin
 *             match a with
 *             | Action (symb,indices) ->
 *               begin
 *                 let action = Action.of_term symb indices table in
 *                 match Symbols.Macro.get_def mn table with
 *                 | Symbols.Cond -> SystemExpr.Condition (ncond, action)
 *                                   :: parse_substd0 q
 *                 | _ -> failure ()
 *               end
 *             | _ -> assert false
 *           end
 *         | exception _ ->
 *           begin
 *             match Theory.convert conv_env tsubst mterm Sorts.Message,
 *                   Theory.convert conv_env tsubst b Sorts.Message with
 *             |Term.Macro ((mn, sort, is),l,a), nout ->
 *               begin
 *                 match a with
 *                 | Action (symb,indices) ->
 *                   begin
 *                     let action = Action.of_term symb indices table in
 *                     match Symbols.Macro.get_def mn table with
 *                     | Symbols.Output -> SystemExpr.Output (nout, action)
 *                                         :: parse_substd0 q
 *                     | _ -> failure ()
 *                   end
 *                 | _ -> assert false
 *               end
 *             | _ -> failure ()
 *           end
 *         | _ ->  failure ()
 *       end
 *     | _ ->  failure ()
 *   in
 *   parse_substd0 s
 * 
 * (* Given a list of index names, and some remainder, instantiates the variables
 *    and produce the substitution. *)
 * let rec parse_indexes =
 *   function
 *   | [] -> ([],[],[])
 * 
 *   | Args.Theory (L.{ pl_desc = Theory.App (i,[]) } ) :: q ->
 *     let i = L.unloc i in
 *     let id,vs,rem = parse_indexes q in
 *     let var =  snd (Vars.make_fresh Vars.empty_env Sorts.Index i) in
 *     Theory.ESubst (i, Term.Var var)::id
 *   , (Vars.EVar var)::vs, rem
 *   | a :: q -> let id,vs, rem = parse_indexes q in
 *     id,vs,a::rem *)

(* let equiv_goal_from_subst system table vs substd =
 *   let make_equiv a b =
 *     Term.And (Term.Impl (a, b), Term.Impl (b, a))
 *   in
 *   let rec conj_equiv =
 *     function
 *     | [] -> Term.True
 *     | SystemExpr.Condition (ncond, action) :: q ->
 *       let taction = SystemExpr.action_to_term table system action in
 *       let new_eq = make_equiv
 *                   (Term.Macro (Term.cond_macro,[],taction))
 *                   ncond
 *       in
 *       if q <> [] then
 *         Term.And (new_eq, conj_equiv q)
 *       else
 *         new_eq
 *     | SystemExpr.Output (nout, action) :: q ->
 *       let taction = SystemExpr.action_to_term table system action in
 *       let new_eq = Term.Atom (`Message (`Eq,
 *                                         nout,
 *                                         (Term.Macro (Term.out_macro,[],taction))
 *                                        ))
 *       in
 *       if q <> [] then
 *         Term.And (new_eq , conj_equiv q)
 *       else
 *         new_eq
 *   in
 *   Term.ForAll (vs, conj_equiv substd)
 * 
 * let system_subst new_system isubst vs subst s =
 *   let substdescr = parse_substd (TraceSequent.table s) isubst subst in
 *   try
 *     let table, new_system =
 *       SystemExpr.clone_system_subst
 *         (TraceSequent.table s) (TraceSequent.system s)
 *         new_system substdescr in
 * 
 *     let new_system_e =
 *       match TraceSequent.system s with
 *       | Pair _ | SimplePair _ ->
 *         SystemExpr.simple_pair table new_system
 *       | Single (Left _) ->
 *         SystemExpr.single table (Left new_system)
 *       | Single (Right _) ->
 *         SystemExpr.single table (Right new_system)
 *     in
 *     let new_goal = TraceSequent.set_table table s
 *                    |> TraceSequent.set_system new_system_e in
 * 
 *     TraceSequent.set_conclusion
 *       (equiv_goal_from_subst new_system_e table vs substdescr) s :: [new_goal]
 *   with SystemExpr.SystemNotFresh ->
 *     hard_failure
 *       (Tactics.Failure "System name already defined for another system.")
 * 
 * let () =
 *   T.register_general "systemsubstitute"
 *     ~tactic_help:{general_help = "Apply a substituion to the current system and \
 *                                   checks its validity.";
 *                   detailed_help =
 *                     "Modify the system of the current proof, so that the given \
 *                      substitution over some cond@T or output@T has been applied, \
 *                      and produces the subgoals asking that the substitution \
 *                      preserves equality of distributions. The system produced is \
 *                      named after the given name, and if a previous system was \
 *                      already defined in the same way it does not recreate it.
 *            \n\nUsage: systemsubstitute new_sytem_name,i1,...,ik,\
 *                      cond@T, newcond, output@T, newoutput, ... ";
 *                   usages_sorts = [];
 *                   tactic_group = Structural}
 *     (function
 *       | Args.Theory (L.{ pl_desc = App (system_name,[]) } ) :: q  ->
 *         let subst_index, vs, subst_descr = parse_indexes q in
 *         let system_name = L.unloc system_name in
 * 
 *         fun s sk fk -> begin
 *             match system_subst system_name subst_index vs subst_descr s with
 *              | subgoals -> sk subgoals fk
 *              | exception Tactics.Tactic_soft_failure e -> fk e
 *            end
 *        | _ -> hard_failure (Tactics.Failure "improper arguments")) *)

(*------------------------------------------------------------------*)
(* TODO: this should be an axiom in some library, not a rule *)
let exec (Args.Timestamp a) s =
  let _,var = Vars.(make_fresh (TraceSequent.env s) Sorts.Timestamp "t") in
  let formula =
    ForAll
      ([Vars.EVar var],
       Impl (Atom (Term.mk_timestamp_leq (Var var) a),
             Macro(Term.exec_macro,[],Var var)))
  in
  [happens_premise s a ;

   TraceSequent.set_conclusion Term.(Macro (exec_macro,[],a)) s;
  
    TraceSequent.set_conclusion
      (Term.mk_impl formula (TraceSequent.conclusion s)) s]

let () =
  T.register_typed "executable"
    ~general_help:"Assert that exec@_ implies exec@_ for all \
                   previous timestamps."
    ~detailed_help:"This is by definition of exec, which is the conjunction of \
                    all conditions before this timestamp."
    ~tactic_group:Structural
    exec Args.Timestamp


(*------------------------------------------------------------------*)
(** [fa s] handles some goals whose conclusion formula is of the form
  * [C(u_1..u_N) = C(v_1..v_N)] and reduced them to the subgoals with
  * conclusions [u_i=v_i]. We only implement it for the constructions
  * [C] that congruence closure does not support: conditionals,
  * sequences, etc. *)
let fa s =
  let unsupported () =
    Tactics.(soft_failure (Failure "equality expected")) in

  match TraceSequent.conclusion s with
    | Term.Atom (`Message (`Eq,u,v)) ->
        begin match u,v with

          | Term.ITE (c,t,e), Term.ITE (c',t',e') ->
            let subgoals =
              let open TraceSequent in
              [ s |> set_conclusion (Term.mk_impl c c') ;

                s |> set_conclusion (Term.mk_impl c' c) ;

                s |> set_conclusion (Term.mk_impls
                                       (if c = c' then [c] else [c;c'])
                                       (Term.Atom (`Message (`Eq,t,t'))));

                s |> set_conclusion (Term.mk_impls [Term.Not c;Term.Not c']
                                       (Term.Atom (`Message (`Eq,e,e')))) ]
            in
            subgoals

          | Term.Seq (vars,t),
            Term.Seq (vars',t') when vars = vars' ->
            let env = ref (TraceSequent.env s) in
            let vars' = List.map (Vars.make_fresh_from_and_update env) vars in
            let s = TraceSequent.set_env !env s in
            let subst =
              List.map2
                (fun i i' -> ESubst (Term.Var i, Term.Var i'))
                vars vars'
            in
            let t = Term.subst subst t in
            let t' = Term.subst subst t' in
            let subgoals =
              [ TraceSequent.set_conclusion
                  (Term.Atom (`Message (`Eq,t,t'))) s ]
            in
            subgoals

          | Term.Find (vars,c,t,e),
            Term.Find (vars',c',t',e') when vars = vars' ->
            (* We could simply verify that [e = e'],
             * and that [t = t'] and [c <=> c'] for fresh index variables.
             *
             * We do something more general for the conditions,
             * which is useful for cases arising from diff-equivalence
             * where some indices are unused on one side:
             *
             * Assume [vars = used@unused]
             * where [unusued] variables are unused in [c] and [t].
             *
             * We verify that [forall used. (c <=> exists unused. c')]:
             * this ensures that if one find succeeds, the other does
             * too, and also that the selected indices will match
             * except for the [unused] indices on the left, which does
             * not matter since they do not appear in [t]. *)

            (* Refresh bound variables. *)
            let env = ref (TraceSequent.env s) in
            let vars' = List.map (Vars.make_fresh_from_and_update env) vars in
            let s = TraceSequent.set_env !env s in
            let subst =
              List.map2
                (fun i i' -> ESubst (Term.Var i, Term.Var i'))
                vars vars'
            in
            let c  = Term.subst subst c in
            let c' = Term.subst subst c' in
            let t  = Term.subst subst t in
            let t' = Term.subst subst t' in

            (* Extract unused variables. *)
            let used,unused =
              let occ_vars = Term.get_vars c @ Term.get_vars t in
              let vars = List.map (fun i -> Vars.EVar i) vars' in
              List.partition
                (fun v -> List.mem v occ_vars)
                vars
            in

            let subgoals =
              let open TraceSequent in
              [ s |> set_conclusion
                       (Term.mk_impl c (Term.mk_exists unused c')) ;

                s |> set_conclusion (Term.mk_impl c' c) ;

                s |> set_conclusion (Term.mk_impls [c;c']
                                       (Atom (`Message (`Eq,t,t'))));

                s |> set_conclusion (Term.Atom (`Message (`Eq,e,e'))) ]
            in
            subgoals

          | _ -> Tactics.(soft_failure (Failure "unsupported equality"))
        end
    | _ -> unsupported ()

let () =
  T.register "fa"
    ~tactic_help:{general_help = "Break down some conclusion equalities into the \
                                  equalities of their subterms.";
                  detailed_help = "When we have G => f(u) = f(v), produces the \
                                   goal G => u=v. Produces as many subgoals as \
                                   arugment of the head function symbol. Recall \
                                   that everything is a function, notably, if \
                                   then else and try find construct are.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    fa


(*------------------------------------------------------------------*)
(** New goal simplification *)
    
let new_simpl ~congr ~constr s =
  let goals = Term.decompose_ands (TraceSequent.conclusion s) in
  let goals = List.filter_map (fun goal ->
      if Hyps.is_hyp goal s || Term.f_triv goal then None
      else match goal with
        | Term.Atom Term.(#trace_atom as at) -> 
          if constr && Constr.query ~precise:true (get_models s) [`Pos, at] 
          then None 
          else Some goal

        | Term.Atom (`Message (`Eq, t1, t2)) -> 
          if congr && Completion.check_equalities (get_trs s) [Term.ESubst (t1,t2)] 
          then None
          else Some goal          

        | _ -> Some goal
    ) goals in
  [TraceSequent.set_conclusion (Term.mk_ands goals) s]


(*------------------------------------------------------------------*)
(** Automated goal simplification *)

let clear_triv s sk fk = sk [Hyps.clear_triv s] fk

(** Simplify goal. *)
let simplify ~close ~strong =
  let open Tactics in
  let intro = Config.auto_intro () in
  
  let assumption = if close then [try_tac (wrap_fail assumption)] else [] in
  let new_simpl ~congr ~constr = 
    if strong && not intro then [wrap_fail (new_simpl ~congr ~constr)] else [] 
  in
  andthen_list (
    (* Try assumption first to avoid loosing the possibility
       * of doing it after introductions. *)
    assumption @ (new_simpl ~congr:false ~constr:false) @ assumption @
    (if close || intro then [wrap_fail intro_all;
                             wrap_fail simpl_left_tac] else []) @
    assumption @
    (* Learn new term equalities from constraints before
     * learning new index equalities from term equalities,
     * otherwise this creates e.g. n(j)=n(i) from n(i)=n(j). *)
    (* (if intro then [wrap eq_trace] else []) @ *)
    (if strong then [wrap_fail eq_names] else []) @
    (* Simplify equalities using substitution. *)
    (repeat (wrap_fail autosubst)) ::
    assumption @ (new_simpl ~congr:true ~constr:true) @ assumption @
    [clear_triv]
  ) 

  (* Attempt to close a goal. *)
  let do_conclude =
    Tactics.orelse_list [wrap_fail congruence_tac; 
                         wrap_fail constraints_tac; 
                         wrap_fail assumption]

(* If [close] then tries to automatically prove the goal,
 * otherwise it may also be reduced to a single subgoal. *)
let rec simpl ~strong ~close : TraceSequent.t Tactics.tac =
  let open Tactics in
  let (>>) = andthen ~cut:true in
  (* if [close], we introduce as much as possible to help. *)
  simplify ~close ~strong >> 

  if not strong
  then (fun g sk fk -> sk [g] fk)
  else 
    (if close || Config.auto_intro ()
     then try_tac do_conclude else Tactics.id) >>
    fun g sk fk ->
    (* If we still have a goal, we can try to split a conjunction
     * and prove the remaining subgoals, or return this goal,
     * but we must respect [close]. *)
    let fk =
      if close 
      then fun _ -> fk GoalNotClosed
      else fun _ -> sk [g] fk
    in
    (wrap_fail goal_and_right) g
      (fun l _ -> match l with
         | [g1;g2] ->
           simpl ~strong ~close g1
             (fun l' _ ->
                if l'=[] then
                  simpl ~strong ~close g2 sk fk
                else
                  simpl ~strong ~close:true g2
                    (fun l'' fk -> assert (l'' = []) ; sk l' fk)
                    fk)
             fk
         | _ -> assert false)
      fk

let () = T.register_general "autosimpl"
    ~tactic_help:{general_help = "Simplify a goal, without closing \
                                  it. Automatically called after each tactic.";
                  detailed_help = "Performs introductions, eqtrace and eqnames.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    (function
      | [] -> simpl ~strong:(Config.auto_intro ()) ~close:false
      | _ -> hard_failure (Tactics.Failure "no argument allowed")) ;

  T.register_general "simpl"
    ~tactic_help:{general_help = "Simplifies a goal.";
                  detailed_help = "Performs introductions, eqtrace and eqnames.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    (function
      | [] -> simpl ~strong:true ~close:false
      | _ -> hard_failure (Tactics.Failure "no argument allowed")) ;

  T.register_general "auto"
     ~tactic_help:{general_help = "Closes a goal.";
                   detailed_help = "Behaves like simpl, but also calls \
                                    congruence, constraints and assumption.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    (function
       | [] -> simpl ~strong:true ~close:true
       | _ -> hard_failure (Tactics.Failure "no argument allowed"))


(*------------------------------------------------------------------*)
let do_s_item (s_item : Args.s_item) s : TraceSequent.sequent list =
  match s_item with
  | Args.Simplify l ->
    dbg "there";
    let tac = simpl ~strong:true ~close:false in
    Tactics.run tac s 

  | Args.Tryauto l ->
    let tac = Tactics.try_tac (simpl ~strong:true ~close:true) in
    Tactics.run tac s 


(*------------------------------------------------------------------*)

(** [rewrite ~all tgt rw_args] rewrites [rw_arg] in [tgt].
    If [all] is true, then does not fail if no rewriting occurs. *)
let rewrite ~all 
    (targets: rw_target list) 
    (rw : Args.rw_count * Ident.t option * rw_erule) s 
  : sequent * sequent list =
  let found1, cpt_occ = ref false, ref 0 in

  (* Return: (f, subs) *)
  let rec do1 
    : type a. Term.formula -> Args.rw_count -> a rw_rule -> 
      Term.formula * Term.formula list = 
    fun f mult (sv, rsubs, l, r) ->
      if !cpt_occ > 1000 then   (* hard-coded *)
          hard_failure (Failure "max nested rewriting reached (1000)");
      incr cpt_occ;

      (* Substitutes all instances of [occ.occ] by [r] (where free variables
         are instantiated according to [occ.mv]. *)
      let rw_inst (occ : a Term.Match.match_occ) =
        found1 := true;
        let subst = Term.Match.to_subst occ.mv in
        let r_f = Term.cast (Term.sort occ.occ) (Term.subst subst r) in
        ( Term.subst [Term.ESubst (occ.occ, r_f)] f, 
          List.map (Term.subst subst) rsubs ) 
      in

      (* tries to find an occurence of [l] and rewrite it. *)
      let occ = Term.Match.find f { p_term = l; p_vars = sv; } in

      match mult, occ with
      | (`Once | `Many), None -> 
        if not all 
        then soft_failure Tactics.NothingToRewrite 
        else f, []

      | (`Many | `Any), Some occ -> 
        let f, subs  = rw_inst occ in
        let f, subs' = do1 f `Any (sv, rsubs, l, r) in
        f, subs @ subs'

      | `Once,          Some occ -> rw_inst occ
      | `Any,           None     -> f, []
  in
  
  let is_same hyp_id target_id = match hyp_id, target_id with
    | None, _ | _, None -> false
    | Some hyp_id, Some target_id ->
      Ident.name hyp_id = Ident.name target_id && 
      Ident.name hyp_id <> "_" 
  in

  let doit (f,tgt_id) =
    match rw with
    | mult,  id_opt, (sv, subs, Term.ESubst (l,r)) ->
      if is_same id_opt tgt_id 
      then f, []
      else do1 f mult (sv, subs, l, r)          
  in
 
  let s, subs = do_targets doit s targets in

  if all && not !found1 then soft_failure Tactics.NothingToRewrite;

  s, subs



(** Parse rewrite tactic arguments as rewrite rules with possible subgoals 
    showing the rule validity. *)
let p_rw_item (rw_arg : Args.rw_item) s : rw_earg * sequent list =
  let to_rule ~loc dir f : rw_erule = 
    let vs, f = Term.decompose_forall f in
    let vs = Vars.Sv.of_list vs in
    
    let forms = List.rev (Term.decompose_impls f) in 
    let subs, f = List.rev (List.tl forms), List.hd forms in

    let e = match f with
      | Term.Atom (`Message   (`Eq, t1, t2)) -> Term.ESubst (t1,t2)
      | Term.Atom (`Timestamp (`Eq, t1, t2)) -> Term.ESubst (t1,t2)
      | Term.Atom (`Index     (`Eq, t1, t2)) -> 
        Term.ESubst (Term.Var t1,Term.Var t2)
      | _ -> hard_failure ?loc (Tactics.Failure "not an equality") 
    in

    let e = match dir with
      | `LeftToRight -> e
      | `RightToLeft -> 
        let Term.ESubst (t1,t2) = e in
        Term.ESubst (t2,t1)
    in

    (* FIXME: slightly incorrect error message *)
    if not (check_erule (vs, subs, e)) then 
      hard_failure Tactics.BadRewriteRule;

    vs, subs, e
  in

  let p_rw_rule dir (rw_type : Theory.formula) 
    : rw_erule * sequent list * Ident.t option = 
    match Args.convert_as_lsymb [Args.Theory rw_type] with
    | Some str when is_hyp_or_lemma str s ->
      let id_opt, f = get_hyp_or_lemma str s in

      (* We are using an hypothesis, hence no new sub-goals *)
      let premise = [] in

      to_rule ~loc:None dir f, premise, id_opt

    | _ -> 
      let conv_env = Theory.{ table = TraceSequent.table s;
                              cntxt = InGoal; } in      
      let subst = Theory.subst_of_env (TraceSequent.env s) in
      let f = Theory.convert conv_env subst rw_type Sorts.Boolean in

      (* create new sub-goal *)
      let premise = [TraceSequent.set_conclusion f s] in

      to_rule ~loc:(Some (L.loc rw_type)) dir f, premise, None
  in

  let p_rw_item (rw_arg : Args.rw_item) : rw_earg * (sequent list) = 
    let rw, subgoals = match rw_arg.rw_type with
      | `Form f -> 
        let dir = L.unloc rw_arg.rw_dir in
        (* (rewrite rule, subgols, hyp id) if applicable *)
        let rule, subgoals, id_opt = p_rw_rule dir f in
        Rw_rw (id_opt, rule), subgoals

      | `Expand t -> 
        if L.unloc rw_arg.rw_dir <> `LeftToRight then
          hard_failure ~loc:(L.loc rw_arg.rw_dir) 
            (Failure "expand cannot take a direction");
        
         Rw_expand t, []
    in
    (rw_arg.rw_mult, rw), subgoals
  in
  
  p_rw_item rw_arg

(** Applies a rewrite item *)
let do_rw_item 
    (rw_item : Args.rw_item) (rw_in : Args.rw_in) (s : TraceSequent.sequent) 
  : TraceSequent.sequent list =
  let targets, all = match rw_in with
    | Some (`Hyps symbs) -> 
      List.map (fun symb -> `Hyp (fst (Hyps.by_name symb s))) symbs, false
    | Some `All -> target_all s, true
    | None -> [`Goal], false
  in

  let (rw_c,rw_arg), subgoals = p_rw_item rw_item s in

  match rw_arg with
  | Rw_rw (id, erule) -> 
    let s, subs = rewrite ~all targets (rw_c, id, erule) s in
    subgoals @                  (* prove rule *)
    subs @                      (* prove instances premisses *)
    [s]                         (* final sequent *)

  | Rw_expand arg -> [expand targets arg s]

(** Applies a rewrite arg  *)
let do_rw_arg rw_arg rw_in s : TraceSequent.sequent list =
  match rw_arg with
  | Args.R_item rw_item  -> do_rw_item rw_item rw_in s
  | Args.R_s_item s_item -> do_s_item s_item s (* targets are ignored there *)

let rewrite_tac args s sk fk =
  match args with
  | [Args.RewriteIn (rw_args, in_opt)] ->
    let seqs = 
      List.fold_left (fun seqs rw_arg ->
          List.concat_map (do_rw_arg rw_arg in_opt) seqs
        ) [s] rw_args 
    in
    sk seqs fk

  | _ -> hard_failure (Tactics.Failure "improper arguments")

let rewrite_tac args s sk fk =
  try rewrite_tac args s sk fk with
  | Tactics.Tactic_soft_failure (_,e) -> fk e

let () =
  T.register_general "rewrite"
    ~tactic_help:{
      general_help =
        "If t1 = t2, rewrite all occurences of t1 into t2 in the goal.\n\
         Usage: rewrite Hyp Lemma Axiom (forall (x:message), t = t').\n       \
         rewrite Lemma Axiom (t=t').\n       \
         rewrite (forall (x:message), t = t').\n       \
         rewrite (t = t') Lemma in H.";
      detailed_help = "";
      usages_sorts  = [];
      tactic_group  = Structural;}
    rewrite_tac 

(*------------------------------------------------------------------*)
let rec do_intros (intros : Args.intro_pattern list) s =
  match intros with
  | [] -> [s]

  | (Args.SItem s_item) :: intros ->
    do_intros_list intros (do_s_item s_item s)    

  | (Args.Simpl s_ip) :: intros ->
    let ss = do_intro_pat s_ip s in
    do_intros_list intros ss

  | (Args.Star loc) :: intros ->
    try
      let s_ip = Args.(SNamed AnyName) in
      let ss = do_intro_pat s_ip s in
      List.concat_map (do_intros [Args.Star loc]) ss

    with Tactics.Tactic_soft_failure (_,NothingToIntroduce) -> [s]

and do_intros_list intros ss = List.concat_map (do_intros intros) ss

let intro_tac args s sk fk =
  try match args with
    | [Args.IntroPat intros] -> sk (do_intros intros s) fk

    | _ -> Tactics.(hard_failure (Failure "improper arguments"))
  with Tactics.Tactic_soft_failure (_,e) -> fk e

let () =
  T.register_general "intro"
    ~tactic_help:{general_help = "Introduce topmost connectives of conclusion \
                                  formula, when it can be done in an invertible, \
                                  non-branching fashion.\
                                  \n\nUsage: intro a b _ c *";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    intro_tac


(*------------------------------------------------------------------*)
(** Projecting a goal on a bi-system
  * to distinct goals for each projected system. *)

let project s =
  let system = TraceSequent.system s in
  match system with
  | Single _ ->
    soft_failure (Tactics.Failure "goal already deals with a \
                                           single process")
  | _ ->
    let s1 = TraceSequent.set_system
        SystemExpr.(project_system PLeft  system) s in
    let s2 = TraceSequent.set_system
        SystemExpr.(project_system PRight system) s in
    let s1 = TraceSequent.pi PLeft s1 in
    let s2 = TraceSequent.pi PRight s2 in
    [s1;s2]

let () =
  T.register "project"
     ~tactic_help:{general_help = "Project a goal on a bi-system into goals on its projections.";
                   detailed_help = "Is morally equivalent to a general function \
                                    application on the diff operator.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    project

(*------------------------------------------------------------------*)
(** Replacing a conditional by the then branch (resp. the else branch) if the
 * condition is true (resp. false). *)

let apply_yes_no_if b s =
  let cntxt = mk_trace_cntxt s in
  let conclusion = TraceSequent.conclusion s in
  (* search for the first occurrence of an if-then-else in [elem] *)
  let iter = new Iter.get_ite_term ~cntxt in
  List.iter iter#visit_formula [conclusion];
  match iter#get_ite with
  | None ->
    soft_failure
      (Tactics.Failure
        "can only be applied if the conclusion contains at least \
         one occurrence of an if then else term")
  | Some (c,t,e) ->
    (* Context with bound variables (eg try find) are not (yet) supported.
     * This is detected by checking that there is no "new" variable,
     * which are used by the iterator to represent bound variables. *)
    let vars = (Term.get_vars c) @ (Term.get_vars t) @ (Term.get_vars e) in
    if List.exists Vars.(function EVar v -> is_new v) vars then
      soft_failure (Tactics.Failure "application of this tactic \
        inside a context that bind variables is not supported")
    else
      let branch, trace_sequent =
        if b then (t, TraceSequent.set_conclusion c s)
        else (e, TraceSequent.set_conclusion (Term.mk_not c) s)
      in
      let subst = [Term.ESubst (Term.ITE (c,t,e),branch)] in
      [ trace_sequent; TraceSequent.subst subst s ]

let yes_no_if b =
  (function
    | [] ->
      fun s sk fk -> begin match apply_yes_no_if b s with
        | subgoals -> sk subgoals fk
        | exception Tactics.Tactic_soft_failure (_,e) -> fk e
      end
    | _ -> hard_failure (Tactics.Failure "no argument allowed"))

let () =
  T.register "yesif"
    ~tactic_help:{general_help = "Replaces the first conditional occurring in \
                                  the conclusion by its then branch if the \
                                  condition is true.";
                  detailed_help = "Replaces a proof goal with conclusion `if phi \
                                   then u else v` by the goals 'phi <=> true' \
                                   and the original goal now with u instead of \
                                   the conditional.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    (apply_yes_no_if true)

let () =
  T.register "noif"
    ~tactic_help:{general_help = "Replaces the first conditional occurring in \
                                  the conclusion by its else branch if the \
                                  condition is false.";
                   detailed_help = "Replaces a proof goal with condition `if phi \
                                    then u else v` by the goals 'phi <=> false' \
                                    and the original goal now with v instead of \
                                    the conditional.";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    (apply_yes_no_if false)


(*------------------------------------------------------------------*)
(** {2 Cryptographic Tactics} *)

(*------------------------------------------------------------------*)
(** Unforgeability Axioms *)

type unforgeabiliy_param = Term.fname * Term.nsymb * Term.message
                           * Sorts.message Term.term
                           * (Symbols.fname Symbols.t -> bool)
                           * Sorts.boolean Term.term  list * bool

let euf_param table (t : Term.formula) : unforgeabiliy_param =
  let bad_param () =
    soft_failure
      (Tactics.Failure
         "euf can only be applied to an hypothesis of the form h(t,k)=m \
          or checksign(s,pk(k))=m \
          for some hash or signature or decryption functions") in

  let at = match t with
    | Atom (`Message at) -> at
    | _ -> bad_param () in

  match at with
  | (`Eq, Fun ((checksign, _), [s; Fun ((pk,_), [Name key])]), m)
  | (`Eq, m, Fun ((checksign, _), [s; Fun ((pk,_), [Name key])])) ->
    begin match Theory.check_signature table checksign pk with
      | None ->
        Tactics.(soft_failure 
                   (Failure "the message does not correspond \
                             to a signature check with the associated pk"))
      | Some sign -> (sign, key, m, s,  (fun x -> x=pk), [], true)
    end

  | (`Eq, Fun ((hash, _), [m; Name key]), s)
    when Symbols.is_ftype hash Symbols.Hash table ->
    (hash, key, m, s, (fun x -> false), [], true)

  | (`Eq, s, Fun ((hash, _), [m; Name key]))
    when Symbols.is_ftype hash Symbols.Hash table ->
    (hash, key, m, s, (fun x -> false), [], true)

  | _ -> bad_param ()


let intctxt_param table (t : Term.formula) : unforgeabiliy_param =
  let bad_param () =
    soft_failure
      (Tactics.Failure
         "intctxt can only be applied to an hypothesis of the form \
          sdec(s,sk) <> fail \
          or sdec(s,sk) = m (or symmetrically) \
          for some hash or signature or decryption functions") in

  let at = match t with
    | Atom (`Message at) -> at
    | _ -> bad_param () in
  
  let param_dec sdec key m s =
    match Symbols.Function.get_data sdec table with
    | Symbols.AssociatedFunctions [senc] ->
      (senc, key, m, s,  (fun x -> x = sdec),
       [ (Term.Atom (`Message (`Eq, s, Fun (f_fail, []))))], false )
    | Symbols.AssociatedFunctions [senc; h] ->
      (senc, key, m, s,  (fun x -> x = sdec || x = h),
       [ (Term.Atom (`Message (`Eq, s, Fun (f_fail, []))))], false)
      
    | _ -> assert false in
  
  match at with
  | (`Eq, Fun ((sdec, _), [m; Name key]), s)
    when Symbols.is_ftype sdec Symbols.SDec table ->
    param_dec sdec key m s

  | (`Eq, s, Fun ((sdec, is), [m; Name key]))
    when Symbols.is_ftype sdec Symbols.SDec table ->
    param_dec sdec key m s

  | (`Neq, (Fun ((sdec, _), [m; Name key]) as s), Fun (fail, _))
    when Symbols.is_ftype sdec Symbols.SDec table && fail = Term.f_fail->
    param_dec sdec key m s

  | (`Neq, Fun (fail, _), (Fun ((sdec, is), [m; Name key]) as s))
    when Symbols.is_ftype sdec Symbols.SDec table && fail = Term.f_fail ->
    param_dec sdec key m s

  | _ -> bad_param ()

let euf_apply_schema sequent (_, (_, key_is), m, s, _, _, _) case =
  let open Euf in

  (* Equality between hashed messages *)
  let new_f = Term.Atom (`Message (`Eq, case.message, m)) in

  (* Equalities between key indices *)
  let eq_indices =
    List.fold_left2
      (fun cnstr i i' ->
         Term.mk_and cnstr (Term.Atom (`Index (`Eq, i, i'))))
      Term.True
      key_is case.key_indices
  in

  let system = TraceSequent.system sequent in
  let table  = TraceSequent.table sequent in
  (* Now, we need to add the timestamp constraints. *)
  (* The action name and the action timestamp variable are equal. *)
  let action_descr_ts =
    SystemExpr.action_to_term table system case.action_descr.Action.action
  in
  (* The action occured before the test H(m,k) = s. *)
  let maximal_elems =
    Tactics.timeout_get
      (TraceSequent.maximal_elems
         ~precise:false sequent (precise_ts s @ precise_ts m))
  in
  let le_cnstr =
    List.map
      (function ts ->
        Term.Atom (Term.mk_timestamp_leq action_descr_ts ts))
      (maximal_elems)
  in
  let le_cnstr = List.fold_left Term.mk_or Term.False le_cnstr in

  (* TODO: use an existential for new indices. *)
  let sequent = TraceSequent.set_env case.env sequent in

  let goal =
    Term.mk_impls
      [eq_indices; new_f; le_cnstr]
      (TraceSequent.conclusion sequent) in
  TraceSequent.set_conclusion goal sequent

let euf_apply_direct s (_, (_, key_is), m, _, _, _, _) Euf.{d_key_indices;d_message} =
  (* The components of the direct case may feature variables that are
   * not in the current environment: this happens when the case is extracted
   * from under a binder, e.g. a Seq or ForAll construct. We need to add
   * such variables to the environment. *)
  let init_env = TraceSequent.env s in
  let subst,env =
    List.fold_left
      (fun (subst,env) (Vars.EVar v) ->
         if Vars.mem init_env (Vars.name v) then subst,env else
         let env,v' = Vars.make_fresh_from env v in
         let subst = Term.(ESubst (Var v, Var v')) :: subst in
         subst,env)
      ([],init_env)
      (List.sort_uniq Stdlib.compare
         (List.map (fun i -> Vars.EVar i) d_key_indices @
          Term.get_vars d_message))
  in
  let s = TraceSequent.set_env env s in
  let d_message = Term.subst subst d_message in

  (* Equality between hashed messages. *)
  let eq_hashes = Term.Atom (`Message (`Eq, d_message, m)) in

  (* Equality between key indices. *)
  let eq_indices =
    List.fold_left2
      (fun cnstr i i' ->
         let i' = Term.subst_var subst i' in
         Term.mk_and cnstr (Term.Atom (`Index (`Eq, i, i'))))
      Term.True
      key_is d_key_indices
  in

  let goal = Term.mk_impls [eq_indices; eq_hashes] (TraceSequent.conclusion s) in
  TraceSequent.set_conclusion goal s

let euf_apply_facts drop_head s
    ((head_fn, (key_n, key_is), mess, sign, allow_functions, _, _) as p) =
  let env = TraceSequent.env s in
  let cntxt = mk_trace_cntxt s in

  (* check that the SSCs hold *)
  Euf.key_ssc ~messages:[mess;sign] ~allow_functions ~cntxt head_fn key_n;

  (* build the rule *)
  let rule =
    Euf.mk_rule
      ~elems:[] ~drop_head ~allow_functions
      ~cntxt ~env ~mess ~sign
      ~head_fn ~key_n ~key_is
  in

  let schemata_premises =
    List.map (fun case -> euf_apply_schema s p case) rule.Euf.case_schemata
  and direct_premises =
    List.map (fun case -> euf_apply_direct s p case) rule.Euf.cases_direct
  in
  if Symbols.is_ftype head_fn Symbols.SEnc cntxt.table then
    Cca.check_encryption_randomness
      cntxt
      rule.Euf.case_schemata rule.Euf.cases_direct head_fn  [mess;sign] [];
  schemata_premises @ direct_premises

(** Tag EUFCMA - for composition results *)
let euf_apply
    (get_params : Symbols.table -> Term.formula -> unforgeabiliy_param)
    (Args.String hyp_name)
    (s : TraceSequent.t) =
  let table = TraceSequent.table s in
  let id, at = Hyps.by_name hyp_name s in

  let (h,key,m,_,_,extra_goals,drop_head) as p = get_params table at in
  let extra_goals = List.map (fun x ->
      TraceSequent.set_conclusion (Term.mk_impl x (TraceSequent.conclusion s)) s
    ) extra_goals in

  let tag_s =
    let f =
      Prover.get_oracle_tag_formula (Symbols.to_string h)
    in
    (* if the hash is not tagged, the formula is False, and we don't create
       another goal. *)
    if f = Term.False  then
      []
    else
      (* else, we create a goal where m,sk satisfy the axiom *)
      let (Vars.EVar uvarm),(Vars.EVar uvarkey),f = match f with
        | ForAll ([uvarm;uvarkey],f) -> uvarm,uvarkey,f
        | _ -> assert false
      in
      match Vars.sort uvarm,Vars.sort uvarkey with
      | Sorts.(Message, Message) -> let f = Term.subst [
          ESubst (Term.Var uvarm,m);
          ESubst (Term.Var uvarkey,Term.Name key);] f in
        [TraceSequent.set_conclusion
           (Term.mk_impl f (TraceSequent.conclusion s)) s]
      | _ -> assert false in

  (* we create the honest sources using the classical eufcma tactic *)
  try
    let honest_s = euf_apply_facts drop_head s p in
    (tag_s @ honest_s @ extra_goals)
  with Euf.Bad_ssc -> soft_failure Tactics.Bad_SSC

let () =
  T.register_typed "euf"
    ~general_help:"Apply the euf axiom to the given hypothesis name."
    ~detailed_help:"If the hash has been declared with a tag formula, applies \
                    the tagged version.  given tag. Tagged eufcma, with a tag T, \
                    says that, under the syntactic side condition, a hashed \
                    message either satisfies the tag T, or was honestly \
                    produced. The tag T must refer to a previously defined axiom \
                    f(mess,sk), of the form forall (m:message,sk:message)."
    ~tactic_group:Cryptographic
    (euf_apply euf_param) Args.String

let () =
  T.register_typed "intctxt"
    ~general_help:"Apply the intctxt axiom to the given hypothesis name."
    ~detailed_help:"Conditions are similar to euf."
    ~tactic_group:Cryptographic
    (euf_apply intctxt_param) Args.String



(*------------------------------------------------------------------*)
let valid_hash (cntxt : Constr.trace_cntxt) (t : Term.message) = 
  match t with
  | Fun ((hash, _), [m; Name (key,_)]) ->
    Symbols.is_ftype hash Symbols.Hash cntxt.table
    && Euf.check_key_ssc
      ~allow_vars:true ~messages:[m] ~allow_functions:(fun x -> false)
      ~cntxt hash key

  | _ -> false

(** We collect all hashes appearing inside the hypotheses, and which satisfy
    the syntactic side condition. *)
let top_level_hashes s =
  let cntxt = mk_trace_cntxt s in

  let hashes = 
    List.filter (valid_hash cntxt) (TraceSequent.get_all_messages s)
    |> List.sort_uniq Stdlib.compare 
  in   

  if List.length hashes = 0 then soft_failure Tactics.NoSSC;

  let rec make_eq acc hash_list =
    match hash_list with
    | [] -> acc
    | h1::q ->
      List.fold_left
        (fun acc h2 ->
           match h1, h2 with
           | Fun (hash1, [_; Name key1]),
             Fun (hash2, [_; Name key2])
             when hash1 = hash2 && key1 = key2 -> (h1, h2) :: acc
           | _ -> acc)
        (make_eq acc q) q
  in

  let trs = get_trs s in

  make_eq [] hashes
  |> List.filter (fun (a,b) -> 
      Completion.check_equalities trs [Term.ESubst (a,b)])



(** [collision_resistance judge sk fk] applies the collision resistance axiom 
    between the hashes:
    - if [i = Some j], collision in hypothesis [j]
    - if [i = None], collects all equalities between hashes that occur at
    toplevel in message hypotheses. *)
let collision_resistance TacticsArgs.(Opt (String, i)) (s : TraceSequent.t) =  

  let hash_eqs = match i with
    | None -> top_level_hashes s
    | Some (String j) -> match Hyps.by_name j s with
      | _, Term.Atom (`Message (`Eq, t1, t2)) -> 
        let cntxt = mk_trace_cntxt s in
        if not (valid_hash cntxt t1) || not (valid_hash cntxt t2) then 
          soft_failure Tactics.NoSSC;

        [t1,t2]
      | _ -> soft_failure Tactics.NoCollision
  in

  let new_facts =
    List.fold_left
      (fun acc (h1,h2) ->
         match h1, h2 with
         | Fun ((hash1, _), [m1; Name key1]),
           Fun ((hash2, _), [m2; Name key2])
           when hash1 = hash2 && key1 = key2 ->
           Term.Atom (`Message (`Eq, m1, m2)) :: acc
         | _ -> acc)
      [] hash_eqs
  in
  let f_coll = Term.mk_ands new_facts in

  if f_coll = Term.True then soft_failure Tactics.NoCollision;

  let goal = Term.mk_impl f_coll (TraceSequent.conclusion s) in
  [TraceSequent.set_conclusion goal s]

let () = T.register_typed "collision"
    ~general_help:"Collects all equalities between hashes \
                   occurring at toplevel in\
                   message hypotheses, and adds the equalities \
                   between messages that have the same hash with \
                   the same valid key."
    ~detailed_help:"A key is valid if it is only used in a key \
                    position. Remark that this could be relaxed, \
                    as CR holds for any valid key, even known to \
                    the attacker."
    ~tactic_group:Cryptographic
    collision_resistance Args.(Opt String)
