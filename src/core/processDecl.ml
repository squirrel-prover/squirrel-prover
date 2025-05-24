open Utils
open Ppenv

module L    = Location
module Args = TacticsArgs
module SE   = SystemExpr
module Mv   = Vars.Mv
module Sv   = Vars.Sv
module Mt   = Term.Mt

type lsymb = Symbols.lsymb

(*------------------------------------------------------------------*)
(** {Error handling} *)

type error_i =
  | BadEquivForm
  | InvalidCtySpace of string list
  | DuplicateCty of string
  | NonDetOp
  | NotExhaustive of string
  | Failure of string

type dkind = KDecl | KLemma

type error =  L.t * dkind * error_i

let pp_error_i fmt = function
  | BadEquivForm ->
    Fmt.pf fmt "equivalence lemma ill-formed"

  | InvalidCtySpace kws ->
    Fmt.pf fmt "invalid space@ (allowed: @[<hov 2>%a@])"
      (Fmt.list ~sep:Fmt.comma Fmt.string) kws

  | DuplicateCty s -> Fmt.pf fmt "duplicated entry %s" s

  | NonDetOp ->
    Fmt.pf fmt "an operator body cannot contain probabilistic computations"

  | NotExhaustive s
  | Failure s ->
    Fmt.pf fmt "%s" s

let pp_error pp_loc_err fmt (loc,k,e) =
  let pp_k fmt = function
    | KDecl  -> Fmt.pf fmt "declaration"
    | KLemma -> Fmt.pf fmt "lemma declaration" in

  Fmt.pf fmt "%a@[<hov 2>%a failed: %a@]"
    pp_loc_err loc
    pp_k k
    pp_error_i e

exception Error of error

let error loc k e = raise (Error (loc,k,e))

let () =
  Errors.register (function
    | Error e -> Some { printer =
      fun pp_loc_error fmt -> pp_error pp_loc_error fmt e }
    | _ -> None)

(*------------------------------------------------------------------*)
(** {2 Declaration parsing} *)

(** [parse_state_decl n [(x1,s1);...;(xn;sn)] s t] declares
    a new state symbol of type [s1->...->sn->s]
    where [si] is [index] and [s] is [message]
    such that value of [s(t1,...,tn)] for init timestamp
    expands to [t\[x1:=t1,...,xn:=tn\]]. *)
let parse_state_decl
    (table : Symbols.table)
    ({ name; args = p_args; out_ty; init_body; } : Decl.state_macro_decl)
  =
  let ts_init = Term.mk_action Symbols.init_action [] in

  (* open a typing environment *)
  let ienv = Infer.mk_env () in
  
  let env = Env.init ~table () in
  let conv_env = Typing.{ env; cntxt = InProc ([], ts_init); } in

  let env, args = Typing.convert_bnds ~ienv ~mode:NoTags env p_args in
  let conv_env = { conv_env with env } in

  (* parse the macro type *)
  let out_ty = omap (Typing.convert_ty env) out_ty in

  let t, out_ty = Typing.convert ~ienv ?ty:out_ty conv_env init_body in

  (* close the typing environment and substitute *)
  let tsubst =
    match Infer.close env ienv with        
    | Infer.Closed subst -> subst

    | _ as e ->
      Typing.error (L.loc init_body) (Failure (Fmt.str "%a" Infer.pp_error_result e))
  in
  let t = Term.gsubst tsubst t in
  let args = List.map (Subst.subst_var tsubst) args in

  (* FIXME: generalize allowed types *)
  List.iter2 (fun v (_, pty) ->
      if not (Type.equal (Vars.ty v) Type.tindex) then
        Typing.error (L.loc pty) (BadPty [Type.tindex])
    ) args p_args;

  let data =
    Symbols.Macro
      (State (List.length p_args,out_ty, Macros.StateInit_data (args,t)))
  in
  let table, _ = Symbols.Macro.declare ~approx:false table name ~data in
  table

(*------------------------------------------------------------------*)
(* FIXME: merge with corresponding code in `reify.ml` once the
   corresponding git branch is merged. *)
(** Check if an action [a] is compatible with the system [system]. *)
let is_compatible
    (table : Symbols.table) (se_vars : SE.tagged_vars)
    (system : SE.t) (a : Symbols.action)
  : bool
  =
  let _, action = Action.get_def a table in
  match SE.get_compatible_system se_vars system with
  | Some compatible_system ->
    let compatible_system = SE.of_system table compatible_system in
    begin 
      try
        ignore (SE.action_to_term table compatible_system action : Term.term);
        true
      with Not_found -> false
    end

  | None ->
    (* the only action that is compatible with all systems is [init] *)
    a = Symbols.init_action
          
(*------------------------------------------------------------------*)
(** Check that [pat] is a valid match pattern:
   - pattern variable names are unique (except for '_') 
   - pattern variables may occur at-most once
   - [pat] only uses constructors
   - action constructors must exists in [system] *)
let check_match_pattern
    loc (table : Symbols.table)
    (se_vars : SE.tagged_vars) (system : SE.t option)
    (vars : Vars.vars)
    (pat : Term.t) : unit
  =
  List.iter2 (fun v1 v2 -> 
      if not (Vars.equal v1 v2) && 
         not (Vars.is_hole v1) &&
         Vars.name v1 = Vars.name v2 
      then
        error loc KDecl
          (Failure ("multiple occurrences of the pattern variable " ^ Vars.name v1));
    ) vars vars;

  let failed ?(in_system = "") t =
    let ppe = default_ppe ~table () in
    error loc KDecl
      (Failure (Fmt.str "not a constructor%s: %a" in_system (Term._pp ppe) t))
  in
    
  (* check that [t] uses only constructors and variables *)
  let rec valid (t : Term.t) =
    match t with
    | Int _ | Var _ -> ()
    | Action (a,_) ->
      if system = None then
        error loc KDecl (Failure (Fmt.str "missing system annotation"));

      let system = oget system in
      if not (is_compatible table se_vars system a) then
        let in_system =
          match SE.get_compatible_system se_vars system with
          | None -> "in system any"
          | Some c -> Fmt.str " in system %a" Symbols.pp_path c
        in
        failed ~in_system t;

    (* Int.( x1 + i1) where [i1] is a concrete value *)
    | Term.App (Fun (fs,_), [Var _; Int _]) when fs = Library.Int.add table -> ()

    (* [true], [false] *)
    | Fun (fs,_) when fs = Symbols.fs_true || fs = Symbols.fs_false -> ()

    | Fun (_fs,_) -> if false then failed t    (* FEATURE: add ADT constructors *)

    | Tuple _
    | App _ -> Term.titer valid t
    | _ -> failed t
  in
  valid pat


(** Substitute the temporary variable [f_rec] used to
    represent recursive calls by the actual recursif
    function [name] being registered.

    E.g. [App (Var f_rec, args)] may be substituted by [Macros
    (name, args)]. *)
let build_recursive_body
    (table : Symbols.table)
    (f_rec : Vars.var) 
    (name : [`Macro of Term.msymb | `Fname of Symbols.fname ])
    ~(nb_args : int)
    (t : Term.t)
  : Term.t
  =         
  let rec doit t =
    match Term.decompose_app t with
    | Var f, args when Vars.equal f f_rec ->
      let args_f, args_tail = List.takedrop nb_args args in
      let args_f0, arg_f_rec = List.takedrop (nb_args - 1) args_f in
      let arg_f_rec = as_seq1 arg_f_rec in
      let t0 =
        match name with
        | `Macro m -> Term.mk_macro m args_f0 arg_f_rec
        | `Fname name ->
          (* TODO: ty_args *)
          Term.mk_fun table name ~ty_args:(assert false) args_f
      in 
      Term.mk_app t0 args_tail

    | _, _ -> Term.tmap doit t
  in
  doit t

(*------------------------------------------------------------------*)
module PatternMatching = struct
  (** [Action] constructors have a non-standard axiomatization:

     - timestamp are partitioned into non-happening timestamps, and
       happening timestamps. Only the latter boasts of a standard
       constructor axiomatization.

     - further, which constructors partition the set of happening actions
       depends on the system compatibility class the lemma is stated
       in. 

     E.g. if [P] has two actions [A i] and [B], then the following
     pattern-match is exhaustive (and cannot be simplified while
     remaining so):
     [match t with
      | A _ when happens t -> ... 
      | B   when happens t -> ...
      | _   when not happens t -> ...] *)

  (*------------------------------------------------------------------*)
  (** A case term is a match pattern (see [check_match_pattern]) used
      to check the exhaustiveness of a pattern-matching.

      A case term [{term; conds}] comes with conditions
      [conds] for some of its subterms.

      E.g.: 
      
      - if [_] is of type [bool], [{term = (true, _); happens = ∅}]
      represents the values [(true, false)] and [(true, true)];

      - if [_] is of type [timestamp], 
          [{term = (A i, _); happens = {A i ↦ `Happens, _ ↦ `NotHappens}}] 
        represents the values [(A i, τ)] for any [τ] such
        that [A i] happens and [τ] does not. *)
  type case = { 
    term  : Term.term;
    conds : [`Happens | `NotHappens] Term.Mt.t;
  }

  let _pp_case ppe fmt (c : case) =
    if Mt.is_empty c.conds then Term._pp ppe fmt c.term
    else
      let happens, not_happens = 
        List.partition
          (function (_,`Happens) -> true | _ -> false) 
          (Mt.bindings c.conds)
      in
      let pp_happens fmt =
        if happens = [] then () else
          Fmt.pf fmt "@[happens(@[%a@])@]"
            (Fmt.list ~sep:(Fmt.any ",@,") (Term._pp ppe))
            (List.map fst happens)
      in
      let pp_not_happens fmt =
        if not_happens = [] then () else
          Fmt.pf fmt "@[not happens(@[%a@])@]"
            (Fmt.list ~sep:(Fmt.any ",@,") (Term._pp ppe)) 
            (List.map fst not_happens)
      in
      Fmt.pf fmt "@[<hv 2>%a when@ %t%s%t@]" 
        (Term._pp ppe) c.term 
        pp_happens
        (if happens <> [] && not_happens <> [] then " and " else "")
        pp_not_happens


  let[@warning "-32"] pp_case     = _pp_case (default_ppe ~dbg:true ())
  let[@warning "-32"] pp_case_dbg = _pp_case (default_ppe ~dbg:true  ())

  (*------------------------------------------------------------------*)
  (** Check if [case ⊆ pat] *)
  let is_instance 
      (_table : Symbols.table) (_system : SE.t option) 
      ~(case : case) ~(pat : case)
    : bool
    =
    let exception Failed in
    let failed () = raise Failed in

    (* maps right variables (from [pat]) to subterms of [case.term] *)
    let mv = Hashtbl.create 16 in

    (* case, pat *)
    let rec doit t1 t2 =
      match t1, t2 with
      | _, Term.Var v2 -> 
      (* Since that [case.term] and [pat.term] must both be matching
         patterns, thus no variable may appear more than once in
         [case.term] (the same must hold for [pat]). *)
        assert (not (Hashtbl.mem mv v2));
        Hashtbl.add mv v2 t1

      | Term.Action (a1, l1), Term.Action (a2, l2) ->
        if a1 <> a2 then failed ();
        List.iter2 doit l1 l2

      | Term.App (u1, l1), Term.App (u2, l2) ->
        doit u1 u2;
        List.iter2 doit l1 l2

      | Term.Tuple l1, Term.Tuple l2 -> 
        List.iter2 doit l1 l2

      | Term.Fun (f1, _), Term.Fun (f2, _) ->
        if not (Symbols.path_equal f1 f2) then failed ()

      | _ -> failed ()
    in
    try
      doit case.term pat.term;

      (* substitution from right (i.e. [pat]) to left (i.e. [case]) *)
      let subst = 
        Hashtbl.fold
          (fun v t subst -> Term.ESubst (Term.mk_var v, t) :: subst)
          mv []
      in

      (* check if [case.happens ⊧ pat.happens] *) 
      let pat_conds = 
        Mt.fold (fun t prop conds ->
            Mt.add (Term.subst subst t) prop conds
          ) pat.conds Mt.empty 
      in
      Mt.for_all (fun t prop ->
          Mt.exists
            (fun t' prop' -> Term.equal t t' && prop = prop') 
            case.conds 
        ) pat_conds
    with Failed -> false

  (*------------------------------------------------------------------*)
  let wildcard (ty : Type.ty) : Term.t =
    Term.mk_var (Vars.make_fresh ty "_")

  (*------------------------------------------------------------------*)
  (** In case [l = [l1;...;lm]] where [li] represents a multi-set,
      computes the multi-set cartesian product [l1 x ... x ln]. *)
  let cartesian_product (l : 'a list list) : 'a list list =
    List.fold_left (fun product li  ->
        List.concat_map (fun product_elem ->
            List.map (fun x -> x :: product_elem) li
          ) product
      ) [[]] (List.rev l)

  (*------------------------------------------------------------------*)
  exception UnfoldFailed 

  (** Unfolding a case term [t] amounts to specializing (further) [t]
      into a list of exhaustive and mutually exclusive case terms.

      For examples:
      - [Var v] of type [bool] unfolds into [true; false].
      - [Tuple (Var v1, Var v2)] where [v1,v2] are also of type [bool]
        unfolds into [(true,true); (true,false); (false, true); (false,false)].

      @raise UnfoldFailed if case unfolding is not possible *)
  let unfold_case
      (table : Symbols.table) 
      (system : SE.t option) (se_vars : SE.tagged_vars)
      (t : case) 
    : case list 
    =
    (* We do not try to unfold [_ when not (happens _)], as this
       pattern is already "minimal". *)
    if
      Mt.exists
        (fun k prop -> Term.equal k t.term && prop = `NotHappens) 
        t.conds 
    then
      raise UnfoldFailed;

    let merge (merge_terms : Term.t list -> Term.t) (l : case list) : case = 
      let conds = 
        List.fold_left
          (fun mt x -> 
             Mt.merge
               (fun _ prop prop' -> 
                  assert (prop = None || prop' = None);
                  Some (if prop = None then oget prop' else oget prop))
               mt x.conds)
          Mt.empty l 
      in
      let term = merge_terms (List.map (fun x -> x.term) l) in
      { term; conds; }
    in

    let conds = t.conds in

    (* replace a variable of type [ty] by an exhaustive list of
       mutually exclusive cases *)
    let rec unfold_wildcard (ty : Type.ty) : case list =
      match ty with
      | Type.Timestamp ->
        if system = None then raise UnfoldFailed;
        (* Replace [system] by a concrete compatible system.
           E.g. if [system] is a system variable with constraints
           [like/P], replace [system] by [P]. *)
        let system =
          match SE.get_compatible_system se_vars (oget system) with
          | Some system -> system
          | None -> raise UnfoldFailed
        in

        (* compute the list of actions available in [system] *)
        let actions = System.symbs table system in

        let default =
          Term.mk_var (Vars.make_fresh Type.ttimestamp "_")
        in

        (* _ when not happens  *)
        { term = default ; conds = Mt.add default `NotHappens conds} ::

        (* [A _ when happens (A _)] for any action [A] *)
        List.map (fun (_,action) ->
            let args =
              List.init
                (Action.arity action table) 
                (fun _ -> wildcard Type.tindex)
            in
            let term = Term.mk_action action args in
            let conds =         (* init always happens *)
              if action = Symbols.init_action 
              then conds 
              else Mt.add term `Happens conds
            in
            { term; conds; }
          ) (System.Msh.bindings actions)

      | Type.Boolean -> [{ term = Term.mk_true; conds; } ;
                         { term = Term.mk_false; conds; } ]

      | Type.Tuple l -> 
        let cases = List.map unfold_wildcard l in
        List.map (merge Term.mk_tuple) (cartesian_product cases)

      (* FIXME: add cases for ADTs *)

      (* we do not know how to generate unfolding of the remaining
         types, so we fail *)
      | _ -> raise UnfoldFailed
    in

    (* replace a pattern [t] by an equivalent list of specialized
       patterns. *)
    let rec unfold (t : case) : case list =
      match t.term with
      | Var v -> unfold_wildcard (Vars.ty v)
      | Tuple l ->
        unfold_list (fun l -> Term.mk_tuple l) l t.conds 

      | Action (a,l) ->
        unfold_list (fun l -> Term.mk_action a l) l t.conds 

      (* FIXME: add rule for ADTs by changing [false] to something
         appropriate *)
      | App (Fun (f,app_fty),l) -> (* [f] is a constructor *)
         unfold_list (fun l -> Term.mk_fun0 f app_fty l) l t.conds

      (* We decide to fail early here, since [t] cannot be unfolded
         and we already know that [t] is not an instance of any other
         pattern. *)
      | Fun _ -> raise UnfoldFailed

      | _ -> assert false       (* cannot happen *)

    and unfold_list 
        (merge_terms : Term.t list -> Term.t)
        (l : Term.t list) (conds : _ Mt.t) : case list 
      =
      let l = List.map (fun term -> unfold {term; conds}) l in
      List.map (merge merge_terms) (cartesian_product l)
    in
    unfold t

  (*------------------------------------------------------------------*)
  let max_list (l : int list) : int =
    List.fold_left max (-1) l

  (** Must behave similarly to [unfold_case]. *)
  let max_depth
      (_table : Symbols.table) (bodies : Macros.body list)
    =
    let rec depth (pat : Term.t) : int =
      match pat with
      | Int _ | Var _ -> 0

      (* do not add [1] for tuples, as we handle them transparently *)
      | Tuple l -> max_list (List.map depth l)

      | Action (_, l)
      | App (Fun _, l) -> 1 + max_list (List.map depth l)

      | Fun _ -> 1

      | _ -> assert false       (* cannot happen for patterns *)
    in
    max_list
      (List.map
         (fun case -> 
            match case.Macros.pattern with
            | None -> 0         (* [None] means [_] here *)
            | Some t -> depth t) 
         bodies)

  (*------------------------------------------------------------------*)
exception NonExhaustive      
  (* let exhaustiveness_error loc table (cases : case list) = *)
  (*   let ppe = default_ppe ~table () in *)
  (*   error loc KDecl *)
  (*     (NotExhaustive  *)
  (*        (Fmt.str "@[<v 2>pattern-matching is not exhaustive:@ @[<v 0>%a@]"  *)
  (*           (Fmt.list ~sep:Fmt.cut (_pp_case ppe)) cases)) *)

  (*------------------------------------------------------------------*)
  (** Compute conditions equivalent to [t], if possible. *)
  let get_conds (t : Term.t) : _ Mt.t option =
    let exception Abort in

    let rec doit acc : Term.t -> _ = function
      (* [not happens(t)] *)
      | App (Fun (neg,_), [App (Fun (fs,_), [t])])
        when Symbols.path_equal neg Term.f_not
          && Symbols.path_equal fs Term.f_happens ->
        Mt.add t `NotHappens acc

      (* [happens(t)] *)
      | App (Fun (fs,_), [t]) 
        when Symbols.path_equal fs Term.f_happens ->
        Mt.add t `Happens acc

      (* [t1 ∧ t2] *)
      | App (Fun (fs,_), [t1;t2]) 
        when Symbols.path_equal fs Term.f_and ->
        doit (doit acc t1) t2

      (* [true] *)
      | Fun (fs,_) when Symbols.path_equal fs Term.f_true -> acc

      | _ -> raise Abort
    in
    try Some (doit Mt.empty t) with Abort -> None
       
  (*------------------------------------------------------------------*)
  let exhaustive
      (_loc : L.t) (table : Symbols.table)
      (system : SE.t option) (se_vars : SE.tagged_vars)
      ~(match_arg : Vars.var)
      ~(bodies : Macros.body list) (* all of type [arg_ty] *)
    : unit 
    =
    let match_arg_ty = Vars.ty match_arg in
    let match_arg_t = Term.mk_var match_arg in

    let patterns =
      List.filter_map (fun (body : Macros.body) ->
          let term =   (* [None] means anything here *)
            match body.pattern with
            | Some p -> p
            | None -> wildcard match_arg_ty
          in
          match get_conds body.when_cond with
          | None -> None (* we cannot compile this pattern, clear-it *)
          | Some conds ->
            let conds =
              match Mt.find_opt match_arg_t conds with
              | None -> conds
              | Some prop -> Mt.add term prop (Mt.remove match_arg_t conds)
            in
            Some { term; conds; } 
        ) bodies
    in
    let max_depth = max_depth table bodies in

    let unfold_case (t : case) : 'a = 
      try unfold_case table system se_vars t with
      | UnfoldFailed -> raise NonExhaustive
    in
    
    (* Check that all [cases] are instances of patterns.

       Any case that is not an instance is speciliazed, up-to depth
       [max_depth], before recursively running [check]. *)
    let rec check ~(depth : int) (cases : case list) =

      if depth > max_depth then `Missing cases else
        (* compute cases that are not handled by one of the pattern *)
        let cases = 
          List.filter
            (fun (case : case) -> 
               not @@
               List.exists
                 (fun pat -> is_instance table system ~case ~pat)
                 patterns)
            cases
        in
        if cases = [] then `Ok else
          let cases = 
            List.concat_map (fun t -> unfold_case t) cases
          in
          check ~depth:(depth + 1) cases
    in

    let init_case = { term = wildcard match_arg_ty; conds = Mt.empty; } in
    match check ~depth:0 [init_case] with
    | `Ok -> ()
    | `Missing _cases -> raise NonExhaustive
end

(*------------------------------------------------------------------*)
(** [match_formula body] states that [match_arg] matches [body.pattern] and
    [body.when_cond] hold *)
let match_formula (match_arg : Vars.var) (body:Macros.body) : Term.t =
  match body.pattern with
  | None -> body.when_cond
  | Some t when Term.is_var t -> Term.subst [Term.ESubst(t,Term.mk_var match_arg) ] body.when_cond
  | Some t -> 
    Term.mk_exists body.vars @@
    Term.mk_and 
      (Term.mk_eq t (Term.mk_var match_arg))
      body.when_cond

let mk_simpl_not t = 
  if Term.equal t Term.mk_true then Term.mk_false
  else if Term.equal t Term.mk_false then Term.mk_true
  else Term.mk_not ~simpl:true t

(** [not_match_formula body] is equivalent to [not (match_formula
    body)], with a more agreable formulation. *)
let not_match_formula (match_arg : Vars.var) (body:Macros.body) : Term.t =
  match body.pattern with
  | None -> mk_simpl_not body.when_cond
  | Some t -> 
    Term.mk_forall ~simpl:true body.vars @@
    Term.mk_or ~simpl:true
      (Term.mk_neq ~simpl:true t (Term.mk_var match_arg))
      (mk_simpl_not body.when_cond)

(*------------------------------------------------------------------*)
let mk_exhaustive_formula (bodies:Macros.body list) (match_arg:Vars.var) =
  Term.mk_forall [match_arg] @@
  Term.mk_ors (List.map (match_formula match_arg) bodies)

(*------------------------------------------------------------------*)
let mk_exclusive_formula (bodies:Macros.body list) (match_arg:Vars.var) =
  let neg_cases = 
    List.map (fun b -> (b, not_match_formula match_arg b)) bodies 
  in

  let rec mk_impl (head : Term.t list) = function 
    | [] ->  []
    | (body, case) :: tail ->
      let subst_pattern form =
        match body.Macros.pattern with
        | None -> form
        | Some t -> 
          Term.subst [Term.ESubst (Term.mk_var match_arg, t)] form
      in
      (* If we have no pattern, there are no pattern variables
         (i.e. [body.args]). 
         If we have a pattern, there we fully substitute [match_arg],
         so we do not quantify over it. *)
      let args = if body.pattern = None then [match_arg] else body.vars in

      let form = 
        Term.mk_forall ~simpl:true args @@
        subst_pattern @@
        Term.mk_impl ~simpl:true
          body.when_cond
          (Term.mk_ands ~simpl:true
             (head @ (List.map snd tail)))
      in
      form :: mk_impl (case::head) tail
  in  
  Term.mk_ands (mk_impl [] neg_cases)

(*------------------------------------------------------------------*)
let mk_wf_goal table env (rec_op:Symbols.fname) rec_domain_ty =
  
  let elem = Vars.make_fresh rec_domain_ty "x"  in
  let elem' = Vars.make_fresh rec_domain_ty "y" in
  Printer.prt `Default "ok";
  let fun_rec_op = Term.mk_lambda [elem'; elem] (Term.mk_fun_infer_tyargs table rec_op [Term.mk_var elem'; Term.mk_var elem]) in
  Printer.prt `Default "ok";
  let wf_formulas =
    Term.mk_fun_infer_tyargs table (Library.Logic.fs_well_founded table) [fun_rec_op]
  in        
  [Goal.(Local (LowTraceSequent.init ~env wf_formulas))]




type partial_decl = {
  decl        : Decl.fun_decl;
  env         : Env.t;
  f_rec_ty    : Type.ty option;
  f_rec       : Vars.var option;
  subst       : Term.subst;
  args        : Vars.var list;
  user_out_ty : bool;
  out_ty      : Type.ty;
  match_param : Vars.var lazy_t;
}

type final_decl = {
  pdecl : partial_decl;
  params : Vars.var list;
  dist_param : Vars.var option;
  body        : [
    | `Abstract of
        Type.ty list * Type.ty
    | `Concrete of Term.term
    | `Match of Macros.body list 
    ];
  name        :  Symbols.macro option;
  is_match    : bool;
  info        : Term.macro_info option
}

(* inside the body of [parent_call@rec_arg], a recursive call
   [child_call@arg_call] was found at a position guarderd by
   [when_cond_builder].
   
   For termination, one must prove that [when_cond_builder
   (child_call.decreasing_quantity arg_call) <
   (parent_call.decreasing_quantity rec_arg)] holds.
*)
type rec_call_occ = {
  parent_call : Symbols.macro;
  rec_arg : Vars.var;
  child_call  : Symbols.macro;
  when_cond_builder : Term.term -> Term.term;
  arg_call : Term.term;
}

let get_rec_occs 
    _table env macro_name se (bodies : Macros.body list) (rec_arg : Vars.var) _rec_op decls
  : rec_call_occ list 
  =
  let system, _ = match se with
    | Some se -> se, env
    | None ->
      (* We will need a system in which to work inside *)
      let v = SE.Var.of_ident (Ident.create "'S") in
      SE.var v, Env.{env with se_vars=[(v, [Pair])]}
  in

  let names = List.map
       (fun fdecl
         ->
           oget fdecl.name)
       decls
  in
       
            
  
  let simpl=true in

  let get_occs t when_cond_builder =  
    (* for each macro_name@ts occurence in t under cond with fv,
       builds the formula forall fv, cond => t < rec_arg *)
    Match.Pos.fold
      (fun t' _ fv cond _ occs ->
         match t' with
         | Macro (m, _, ts) when List.mem m.s_symb names ->
             {parent_call=macro_name;
              rec_arg;
              child_call=m.s_symb;
              when_cond_builder=
                (fun conc -> when_cond_builder (Term.mk_forall ~simpl:true fv (Term.mk_impls ~simpl cond conc)));
              arg_call=ts
             }
            :: occs

         | _ -> occs)
      system
      []
      t
  in


  List.fold_left
    (fun acc (b:Macros.body) ->
       match b.pattern with
       | None -> (get_occs b.when_cond (Term.mk_impl ~simpl Term.mk_true))
                 @ (get_occs b.out (Term.mk_impl ~simpl b.when_cond))
                 @ acc
       | Some pat ->
         let mk_pat_forall conc =
           if Term.is_var pat then
               Term.subst [Term.ESubst(pat,Term.mk_var rec_arg) ] conc
           else
             Term.mk_forall b.vars
               (Term.mk_impl ~simpl
                  (Term.mk_eq pat (Term.mk_var rec_arg)) conc )
         in
         (get_occs b.when_cond mk_pat_forall)
         @ (get_occs b.out
              (fun conc -> mk_pat_forall
                  (Term.mk_impl ~simpl b.when_cond conc)))

         @ acc

    )
    [] bodies 

(*------------------------------------------------------------------*)
(** Parse an abstract or concrete list of function declarations. *)
let parse_fun_decls
    table (op_kind : Decl.op_kind) (op_in_system : Decl.op_in_system)
    (op_tyargs : Decl.op_tyargs) (decls : Decl.fun_decl list) 
  : Symbols.table * Goal.t list 
  =
  assert (decls<>[]);
  let loc = L.loc (List.hd decls).op_name in
  let ty_vars = List.map (fun l ->
      Type.mk_tvar (L.unloc l)
    ) op_tyargs
  in

  (* open a typing environment *)
  let ienv = Infer.mk_env () in

  (* parse the system annotation, if any *)
  let se_vars, system, (in_systems : Macros.in_systems) = (* see [Macros.in_systems] *)
    match op_in_system with 
    | `Any -> [], None, Macros.Any

    | `Like p ->
      let p = Symbols.System.convert_path p table in
      let v = SE.Var.of_ident (Ident.create "'S") in
      ( [v, [SE.Var.Compatible_with p]], 
        Some (SE.var v), 
        Macros.Like p )

    | `Systems s ->
      let vars, system = SE.Parse.parse ~implicit:false ~se_env:[] table s in
      assert (vars = []);

      let () = (* check that labels of [system]'s are unique *)
        let p = odflt [] (SE.to_projs_any system) in
        let sorted_p = List.sort_uniq Stdlib.compare p in
        if List.length sorted_p <> List.length p then
          error (L.loc s) KDecl (Failure "the multi-system labels must be distincts")
      in
      let in_systems = Macros.Systems system in

      ([], Some system, in_systems)
  in
  let context = omap (fun set -> SE.{ set; pair = None; }) system in

  let env0 = Env.init ~table ~ty_vars ?system:context ~se_vars () in

  let default_tag = (Vars.Tag.make ~const:true Vars.Global) in

  (* is the declaration recursive *)
  let is_rec = match op_kind with `Let `Rec | `Let `RecWithOrd _ -> true | _ -> false in

  (* for recursive declarations, add all [f] to the environment *)
  let env1, decls =
    if not is_rec then 
      (env0, List.map (fun d -> d, None, None) decls) 
    else
      List.fold_left_map
        (fun (env:Env.t) (decl:Decl.fun_decl) ->   
           let f_rec_ty = Type.univar (Infer.mk_ty_univar ienv) in
           let vars, f_rec =
             Vars.make `Shadow env.vars f_rec_ty (L.unloc decl.op_name) default_tag
           in
           ( { env with vars; }, (decl, Some f_rec_ty, Some f_rec) )
        )
        env0
        decls                 
  in

  (* Translate arguments of the operator.
     Assume global constant variables to be able to check that
     the body represents a deterministic computations later in
     case we are parsing an operator declaration (as constant =>
     deterministic). *)
  let decls =
    List.map
      (fun (decl, f_rec_ty, f_rec) ->
         let (env, subst, args) =
           Typing.convert_ext_bnds
             ~ienv ~mode:(DefaultTag default_tag) 
             env1 decl.Decl.op_args
         in
          (* [user_out_ty : bool] : the user provided an output type *)
          let user_out_ty, out_ty =
            match decl.Decl.op_tyout with
            | None    -> false, Type.univar (Infer.mk_ty_univar ienv)
            | Some ty -> true , Typing.convert_ty ~ienv env ty
         in

         (* for defintions using recursion or pattern-matching, the last
            argument is handled in a particular way *)         
          let match_param =
            lazy (             
              let nb_args = List.length args in
              if nb_args = 0 then
                error loc KDecl (Failure "missing a recursion or matching argument");
              
              let _args0, rec_param = List.takedrop (nb_args - 1) args in
              as_seq1 rec_param
            )
          in
          {decl; env; f_rec_ty; f_rec; subst; args; user_out_ty; out_ty; match_param}
      )
      decls
  in


  (* For recursive declaration, register the type of the recursive
     function in [ienv].  
     More precisely, unify the provided and inferred types for the
     whole function *)
  if is_rec then
    List.iter
      (fun (pd:partial_decl)
        ->
          let f_rec_ty = oget pd.f_rec_ty in
          let f_ty =      (* [f] has type [args → out_ty] *)
            Type.fun_l ( List.map Vars.ty pd.args) pd.out_ty
          in
          if Infer.unify_ty ienv f_ty f_rec_ty = `Fail then
            Typing.ty_error ienv
              loc (Term.mk_var @@ oget pd.f_rec)
              ~expected:f_ty ~got:f_rec_ty
      )
      decls;


  (* translate bodies *)
  let decls =
    List.map
      (fun (pd:partial_decl)
        ->              
          let body =
            match op_kind, pd.decl.Decl.op_body with
            | `Op, `Abstract ->
              if not pd.user_out_ty then 
                error loc KDecl (Failure "abstract operator must be typed");

              let in_tys, out_ty = Type.decompose_funs pd.out_ty in
              `Abstract (in_tys, out_ty)

            | (`Let _ | `Op), `Concrete body ->
              let body, _ =
                Typing.convert ~ienv ~ty:pd.out_ty { env = pd.env; cntxt = InGoal; } body
              in
              let body = Term.subst pd.subst body in
              `Concrete body

            | `Let _, `Match matches -> 

              (* the match bodies *)
              let bodies =
                (* when parsing a pattern, no variable from the current
                   context may appear *)
                let pat_env = { pd.env with vars = Vars.empty_env; } in
                List.map (fun Typing.{ pattern; when_cond; out } ->
                    (* parse the pattern *)
                    let pat = 
                      omap 
                        (fst -|
                         Typing.convert
                           ~option:{Typing.Option.default with pat = true; }
                           ~ienv ~ty:(Vars.ty (Lazy.force pd.match_param))
                           { env = pat_env; cntxt = InGoal; })
                        pattern 
                    in

                    (* pattern variables are new variables created during typing *)
                    let pat_vars =
                      Sv.elements
                        (Sv.filter (fun v -> not (Vars.mem pd.env.vars v)) 
                           (omap_dflt Sv.empty Term.fv pat)) 
                    in
                    let env =
                      let vars =
                        Vars.filter
                          (fun v _ -> List.for_all (fun v' -> Vars.name v <> Vars.name v') pat_vars)
                          pd.env.vars
                      in
                      { pd.env with vars = Vars.add_vars (Vars.Tag.local_vars pat_vars) vars; } 
                    in

                    (* check that [pat] is a valid pattern *)
                    if pattern <> None then
                      check_match_pattern
                        (L.loc @@ oget pattern) table se_vars system pat_vars (oget pat);

                    let when_cond = 
                      omap_dflt
                        Term.mk_true
                        (fst -|
                         Typing.convert ~ienv ~ty:Type.tboolean { env; cntxt = InGoal; }) 
                        when_cond 
                    in
                    let out, _ =
                      Typing.convert ~ienv ~ty:pd.out_ty { env; cntxt = InGoal; } out
                    in

                    let when_cond = Term.subst pd.subst when_cond in
                    let out = Term.subst pd.subst out in

                    let body = Macros.{ vars = pat_vars; pattern = pat; when_cond; out; } in
                    body
                  ) matches
              in
              `Match bodies

            | _ -> assert false       (* other cases have no parser rules *)
          in
          (pd, body))
      decls
  in

  (* check that the typing environment is closed *)
  let tsubst =
    match Infer.close env1 ienv with        
    | Infer.Closed subst -> subst

    | _ as e ->
      error loc KDecl (Failure (Fmt.str "%a" Infer.pp_error_result e))
  in
  

  let table, decls =
    List.fold_left_map
      (fun table (pd, body)
        ->
          let args = List.map (Subst.subst_var tsubst) pd.args in
          let match_param = Lazy.map (Subst.subst_var tsubst) pd.match_param in
          let out_ty = Subst.subst_ty tsubst pd.out_ty in
          
          (* is the declaration defined by pattern-matching *)
          let is_match  = match pd.decl.Decl.op_body with `Match _ -> true | _ -> false in 

          let table, name, info =
            match op_kind with
            | `Op ->
              table, None, None
            | `Let _ -> 
              let table, name =
                Symbols.Macro.reserve ~approx:false table pd.decl.Decl.op_name
              in
              let info = 
                let has_dist_param = is_rec || is_match in
                Term.{
                  is_rec; is_match;
                  has_dist_param; 
                  pp_style = `Standard;
                  (* the `@` notation is currently reserved to builtin (this
                   could be changed) *)
                } 
              in
              table, Some name, Some info
          in
          
          (* the last parameters of macros defined by pattern-matching
             or recurrence have is a distinguished parameter *)
          let params, dist_param = 
            if is_rec || is_match then
              ( List.take (List.length args - 1) args,
                Some (Lazy.force match_param) )
            else (args, None)
          in
          table, (
            {pdecl={pd with args; out_ty; match_param};
             params; dist_param; body; name; is_match; info})            
      )
      table
      decls
  in

  let rec_op, wf_goals =
    match op_kind with       
    | `Let (`RecWithOrd op) ->
      let op = Symbols.Operator.convert_path op table in
      let fty = Symbols.OpData.ftype table op in

      let dist_param = (List.hd decls).dist_param in
      let ty_d dp = Vars.ty (oget dp) in
      if List.exists 
          (fun  d -> 
            not(Type.equal (ty_d dist_param) (ty_d d.dist_param))) decls 
      then
        error loc
          KDecl (Failure "all mutual declarations must use the same recursion order");

      begin
        match fty.fty_out, fty.fty_args with
        | ty_out, [ty1; ty2] when Type.equal ty_out Type.tboolean && Type.equal ty1 ty2 -> 
          op, mk_wf_goal table env1 op (ty_d dist_param)
        | _ ->  
          error loc KDecl
            (Failure "the well-founded recursion order must have a \
                      type of the form 'a -> 'a -> bool");
      end
    | _ -> Symbols.fs_lt, []
  in                  

  let finalize_decl
      table
      fdecl
    =
    match op_kind with
    | `Op ->                    (* deterministic operator *)
      begin
        match fdecl.body with
        | `Abstract (in_tys, out_ty) ->       (* abstract declaration *)
          let in_tys = List.map Vars.ty fdecl.pdecl.args @ in_tys in
          Typing.declare_abstract table
            ~ty_args:ty_vars ~in_tys ~out_ty
            fdecl.pdecl.decl.Decl.op_name fdecl.pdecl.decl.op_symb_type, [], []

        | `Concrete body ->         (* concrete declaration *)
          let body = Term.gsubst tsubst body in

          if not (HighTerm.is_deterministic fdecl.pdecl.env body) then
            error loc KDecl NonDetOp;

          let table, name =
            Symbols.Operator.reserve ~approx:false table fdecl.pdecl.decl.op_name
          in

          let op_data = Operator.{ name; ty_vars; args=fdecl.pdecl.args; out_ty=fdecl.pdecl.out_ty; body; } in
          let ftype = Operator.concrete_ftype op_data in

          (* sanity checks on infix symbols *)
          let in_tys = List.length fdecl.pdecl.args in (* number of arguments *)
          Typing.check_fun_symb in_tys fdecl.pdecl.decl.op_name fdecl.pdecl.decl.op_symb_type;

          let data = 
            Symbols.OpData.Operator {def = Concrete (Operator.Val op_data); ftype; } 
          in
          let table = Symbols.Operator.define table ~data name in

          let ppe = default_ppe ~table () in
          Printer.prt `Result "%a" (Operator._pp_concrete_operator ppe) op_data;

          table, [], []

        | _ -> assert false       (* other cases have no parser rules *)
      end

    | `Let _ -> (* probabilistic operator *)
      begin
        let name,info = oget fdecl.name, oget fdecl.info in

        (** Finalize the construction of term representing the
            function's computation. *)        
        let finalize_term ?(subst = []) (t : Term.t) : Term.t =
          let t = Term.gsubst tsubst (Term.subst subst t) in

          (* substitute the temporary variable representing recursive
             calls by the appropriate construction *)
          if is_rec then
            (* number of arguments for a recursive function *)
            List.fold_left
              (fun t
                fdecl
                ->
                  let name, info = oget fdecl.name, oget fdecl.info in
                  let nb_args = List.length fdecl.pdecl.args in
                  let m = Term.mk_symb name ~info fdecl.pdecl.out_ty in
                  build_recursive_body table (oget fdecl.pdecl.f_rec) (`Macro m) ~nb_args t
              )
              t
              decls
          else t
        in 

        (** Finalize the construction of a function's body. *)
        let finalize_body (body : Macros.body) : Macros.body =
          let env = ref (Vars.of_list_simpl fdecl.pdecl.args) in
          let subst = (* replace hole variables `_` by variation of `x` *)
            List.map
              (fun (v : Vars.var) ->
                 let id = Vars.mk (Ident.create "x") v.ty in
                 let v' = Vars.make_approx_r env id () in
                 Term.ESubst (Term.mk_var v, Term.mk_var v'))
              (List.filter Vars.is_hole body.vars)
          in
          Macros.{
            vars      = List.map (Subst.subst_var tsubst -| Term.subst_var subst) body.vars ;
            pattern   = omap (finalize_term ~subst) body.pattern;
            when_cond = finalize_term ~subst body.when_cond;
            out       = finalize_term ~subst body.out;
          }
        in


        let bodies, ex_formulas =
          match fdecl.body with
          | `Match bodies -> 
            let bodies = List.map finalize_body bodies in
            let match_arg = oget fdecl.dist_param in
            (* check that the pattern matching is exhaustive *)
            let exhs_formulas =
              try
                PatternMatching.exhaustive loc table system se_vars
                  ~match_arg
                  ~bodies; []
              with
                PatternMatching.NonExhaustive ->                  
                [mk_exhaustive_formula bodies match_arg]
            in
            let formulas =
              (mk_exclusive_formula bodies match_arg) :: exhs_formulas
            in
            bodies, formulas

          | `Concrete t ->
            (* We build a single macro body when `name` is defined by
               a single term *)
            [Macros.{
                vars      = [] ;
                pattern   = None;
                when_cond = Term.mk_true;
                out       = finalize_term t;
              }], []

          | _ -> assert false       (* other cases have no parser rules *)
        in

        (* check the termination of the recursive definition *)
        let rec_occs =
          if is_rec then
              get_rec_occs table fdecl.pdecl.env name system bodies (oget fdecl.dist_param) rec_op decls         
          else
            []
        in        

        let decreasing_quantity : Term.term option =
          match fdecl.pdecl.decl.op_terby with
          | _ when not(is_rec) -> None
          | Some t ->
            let q_ty = Type.univar (Infer.mk_ty_univar ienv) in
            Some (
              fst @@ Typing.convert ~ienv ~ty:q_ty { env=fdecl.pdecl.env; cntxt = InGoal; } t
            )
          | None -> let dp = oget fdecl.dist_param in Some (Term.mk_var dp)
        in
        let data0 = 
          Macros.{
            name; 
            params=fdecl.params;
            dist_param=fdecl.dist_param; 
            bodies; 
            in_systems;
            ty = fdecl.pdecl.out_ty; 
            rw_strat = Exact;
            info;
            decreasing_quantity;            
            decreasing_measure=rec_op;
          }
        in

        (* sanity checks on infix symbols *)
        let in_tys = List.length fdecl.params in        (* number of arguments *)
        Typing.check_fun_symb in_tys fdecl.pdecl.decl.op_name fdecl.pdecl.decl.op_symb_type;

        let data = 
          Symbols.Macro (General (Macros.Macro_data (Structured data0)))
        in
        let table = Symbols.Macro.define table ~data name in

        let ppe = default_ppe ~table () in
        Printer.prt `Result "%a@." (Macros._pp_structured_macro_data ppe) data0;

        table, rec_occs, ex_formulas
      end
  in
  let table, rec_occs, ex_formulas =
    List.fold_left
      (fun (table, rec_occs, ex_formulas) full_decl ->
         let table, new_rec_occs, new_ex_formulas =
           finalize_decl table full_decl
         in
         (table, new_rec_occs@rec_occs, new_ex_formulas@ex_formulas)
      )
      (table, [], [])  
      decls
  in
  if is_rec then
    let occs_formulas =
      List.map
        (fun rec_occ ->
           let parent_quantity, _ =
             Macros.get_macro_deacreasing_info table rec_occ.parent_call (Term.mk_var rec_occ.rec_arg)
           in
           let child_quantity, _ =
             Macros.get_macro_deacreasing_info table rec_occ.child_call rec_occ.arg_call
           in
           Term.mk_forall ~simpl:true [rec_occ.rec_arg] @@
           rec_occ.when_cond_builder
             (Term.mk_fun_infer_tyargs table rec_op [child_quantity; parent_quantity])
        )
        rec_occs
    in

    let goals =
      let env = Env.init ~table ~ty_vars ?system:context ~se_vars () in
      let mk_goal acc formulas =          
        if formulas=[] then
          acc
        else
          Goal.(Local (LowTraceSequent.init ~env (Term.mk_ands formulas))) :: acc
      in
      mk_goal (mk_goal wf_goals occs_formulas) ex_formulas
    in      
    table, goals      
  else
    let env = Env.init ~table ~ty_vars ?system:context ~se_vars () in
    let goals =          
      if ex_formulas=[] then
        []
      else
        Goal.(Local (LowTraceSequent.init ~env (Term.mk_ands ex_formulas))) :: []
    in
    table, goals

(*------------------------------------------------------------------*)
let parse_game_decl loc table (decl : Crypto.Parse.game_decl) =
  let g = Crypto.Parse.parse loc table decl in

  let ppe = default_ppe ~table () in
  Printer.prt `Result "%a" (Crypto._pp_game ppe) g;

  let table, _ =
    Symbols.Game.declare ~approx:false
      table decl.Crypto.Parse.g_name ~data:(Crypto.Game g) 
  in
  table

(*------------------------------------------------------------------*)
let parse_namespace_cmd table (cmd : Decl.namespace_info) : Symbols.table =
  match cmd with
  | Decl.Enter n -> Symbols.namespace_enter table n
  | Decl.Exit  n -> Symbols.namespace_exit  table n
  | Decl.Open  n -> Symbols.namespace_open  table (Symbols.convert_npath n table)
  | Decl.Close n -> Symbols.namespace_close table (Symbols.convert_npath n table)

(*------------------------------------------------------------------*)
let parse_predicate_decl table (decl : Decl.predicate_decl) : Symbols.table =
    let name = L.unloc decl.pred_name in

    let ty_params = List.map (fun l ->
        Type.mk_tvar (L.unloc l)
      ) decl.pred_tyargs
    in

    (* open a typing environment *)
    let ienv = Infer.mk_env () in

    let env =
      let system = SE.{
          set  = var SE.Var.set;
          pair = Some (SE.to_pair (var SE.Var.pair)); }
      in
      Env.init ~system ~table ~ty_vars:ty_params ()
    in

    (* parse the system variables declared and build the
       system variables environment *)
    let env, se_params =
      Typing.convert_se_var_bnds env decl.pred_se_args
    in

    (* parse binders for multi-term variables *)
    let (se_info, env), multi_args =
      List.map_fold
        (fun (se_info,env) (se_v,bnds) ->
           let se_v : SE.t =
             let se_name = L.unloc se_v in

             let v = 
               match SE.lookup_string se_name env.Env.se_vars with
               | None -> error (L.loc se_v) KDecl (Failure "unknown system variable")
               | Some v -> v
             in
             
             SE.var v
           in
           let env, args = Typing.convert_bnds ~ienv ~mode:NoTags env bnds in
           let se_info = Mv.add_list (List.map (fun v -> v, se_v) args) se_info in
           (se_info, env), (se_v, args)
        ) (Mv.empty, env) decl.pred_multi_args
    in
    (* parse binders for simple variables *)
    let env, simpl_args =
      Typing.convert_bnds ~ienv ~mode:NoTags env decl.pred_simpl_args
    in

    let body =
      match decl.pred_body with
      | None -> Predicate.Abstract
      | Some b ->
        let b =
          Typing.convert_global_formula
            ~ienv ~system_info:se_info
            { env; cntxt = InGoal; } b
        in
        Predicate.Concrete b
    in

    (* close the typing environment and substitute *)
    let tsubst =
      match Infer.close env ienv with        
      | Infer.Closed subst -> subst

      | _ as e ->
        let loc =
          match decl.pred_body with Some b -> L.loc b | None -> L.loc decl.pred_name
        in
        error loc KDecl (Failure (Fmt.str "%a" Infer.pp_error_result e))
    in
    
    let multi_args =
      List.map (fun (info, args) ->
          info, List.map (Subst.subst_var tsubst) args
        ) multi_args
    in
    let simpl_args = List.map (Subst.subst_var tsubst) simpl_args in
    let body = Predicate.gsubst_body tsubst body in

    let args = Predicate.{ multi = multi_args; simple = simpl_args; } in
    let data = Predicate.mk ~name ~se_params ~ty_params ~args ~body in

    (* sanity checks on infix symbols *)
    let in_tys =
      List.fold_left
        (fun in_tys (_, args) -> in_tys + List.length args)
        (List.length simpl_args) multi_args
    in
    Typing.check_fun_symb in_tys decl.pred_name decl.pred_symb_type;

    let table, _ =
      Symbols.Predicate.declare ~approx:false
        table decl.pred_name
        ~data:(Predicate.Predicate data)
    in

    let ppe = default_ppe ~table () in
    Printer.prt `Result "@[<v 2>new predicate:@;%a@;@]"
      (Predicate._pp ppe) data;

    table

(*------------------------------------------------------------------*)
(** Parse additional type information for procedure declarations
    (enc, dec, hash, ...) *)
let parse_ctys table (ctys : Decl.c_tys) (kws : string list) =
  (* check for duplicate *)
  let _ : string list = List.fold_left (fun acc cty ->
      let sp = L.unloc cty.Decl.cty_space in
      if List.mem sp acc then
        error (L.loc cty.Decl.cty_space) KDecl (DuplicateCty sp);
      sp :: acc
    ) [] ctys in

  let env = Env.init ~table () in

  (* check that we only use allowed keyword *)
  List.map (fun cty ->
      let sp = L.unloc cty.Decl.cty_space in
      if not (List.mem sp kws) then
        error (L.loc cty.Decl.cty_space) KDecl (InvalidCtySpace kws);

      let ty = Typing.convert_ty env cty.Decl.cty_ty in
      (sp, ty)
    ) ctys

(*------------------------------------------------------------------*)
let define_oracle_tag_formula (h : lsymb) table (fm : Typing.term) :
  Symbols.table =
  let env = Env.init ~table () in
  let conv_env = Typing.{ env; cntxt = InGoal; } in
  let form, _ = Typing.convert conv_env ~ty:Type.tboolean fm in
    match form with
     | Term.Quant (ForAll, [uvarm; uvarkey], _) ->
       begin
         match Vars.ty uvarm,Vars.ty uvarkey with
         | Type.(Message, Message) ->
           Oracle.add_oracle (h,form) table
         | _ ->
           ProverLib.error (L.loc fm)
             "The tag formula must be of the form forall
             (m:message,sk:message)"
       end

     | _ ->
       ProverLib.error (L.loc fm)
         "The tag formula must be of the form forall
         (m:message,sk:message)"

(*------------------------------------------------------------------*)
(** {2 Declaration processing} *)


let declare table decl : Symbols.table * Goal.t list =
  match L.unloc decl with
  | Decl.Decl_channel s -> Channel.declare table s, []

  | Decl.Decl_process { id; projs; args; proc} ->
    Process.declare table ~id ~args ~projs proc, []

  | Decl.Decl_action a ->
    let table, symb = Symbols.Action.reserve ~approx:false table a.a_name in
    Action.declare_symbol table symb a.a_arity, []

  | Decl.Decl_axiom pgoal ->
    let pgoal =
      match pgoal.Goal.Parsed.name with
      | Some _ -> pgoal
      | None ->
        (* XXX is this dependence to ProverLib necessary ? *)
        { pgoal with Goal.Parsed.name = Some (ProverLib.unnamed_goal ()) }
    in
    let loc = L.loc (oget pgoal.Goal.Parsed.name) in
    let gc,_ = Goal.make table pgoal in
    Lemma.add_lemma ~loc `Axiom gc table, []

  | Decl.Decl_system sdecl ->
    let projs = Typing.parse_projs sdecl.sprojs in
    let exec_model = 
      match sdecl.system_option with
      | None 
      | Some { pl_desc = "classic"     } -> Action.Classic
      | Some { pl_desc = "postquantum" } -> Action.PostQuantum
      | Some l -> error (L.loc l) KDecl (Failure "unknown system option")
    in
    ProcessSystem.declare_system table exec_model sdecl.sname projs sdecl.sprocess, []

  | Decl.Decl_system_modifier sdecl ->
    let new_lemma, proof_obls, table =
      SystemModifiers.declare_system table sdecl
    in
    let table = omap_dflt table (Lemma.add_lemma `Lemma ^~ table) new_lemma in
    table, proof_obls

  | Decl.Decl_dh (h, g, ex, om, ctys) ->
     let ctys =
       parse_ctys table ctys ["group"; "exponents"]
     in
     let group_ty = List.assoc_opt "group"     ctys
     and exp_ty   = List.assoc_opt "exponents" ctys in
     Typing.declare_dh table h ?group_ty ?exp_ty g ex om, []

  | Decl.Decl_hash (n, tagi, ctys) ->
    let table = match tagi with
      | Some t -> define_oracle_tag_formula n table t
      | None -> table in

    let ctys = parse_ctys table ctys ["m"; "h"; "k"] in
    let m_ty = List.assoc_opt  "m" ctys
    and h_ty = List.assoc_opt  "h" ctys
    and k_ty  = List.assoc_opt "k" ctys in

    Typing.declare_hash table ?m_ty ?h_ty ?k_ty n, []

  | Decl.Decl_aenc (enc, dec, pk, ctys) ->
    let ctys = parse_ctys table ctys ["ptxt"; "ctxt"; "r"; "sk"; "pk"] in
    let ptxt_ty = List.assoc_opt "ptxt" ctys
    and ctxt_ty = List.assoc_opt "ctxt" ctys
    and rnd_ty  = List.assoc_opt "r"    ctys
    and sk_ty   = List.assoc_opt "sk"   ctys
    and pk_ty   = List.assoc_opt "pk"   ctys in

    Typing.declare_aenc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?sk_ty ?pk_ty enc dec pk, []

  | Decl.Decl_senc (senc, sdec, ctys) ->
    let ctys = parse_ctys table ctys ["ptxt"; "ctxt"; "r"; "k"] in
    let ptxt_ty = List.assoc_opt "ptxt" ctys
    and ctxt_ty = List.assoc_opt "ctxt" ctys
    and rnd_ty  = List.assoc_opt "r"    ctys
    and k_ty    = List.assoc_opt "k"    ctys in

    Typing.declare_senc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty senc sdec, []

  | Decl.Decl_name (s, p_ty) ->
    let env = Env.init ~table () in

    let p_args_tys, p_out_ty =
      match p_ty with
      | { pl_desc =
            Typing.P_fun (
              { pl_desc = Typing.P_tuple p_args_ty},
              p_out_ty
            )
        } ->
        p_args_ty, p_out_ty

      | { pl_desc = Typing.P_fun (p_arg_ty, p_out_ty)} ->
        [p_arg_ty], p_out_ty

      | _ -> [], p_ty
    in

    let args_tys = List.map (Typing.convert_ty env) p_args_tys in
    let out_ty = Typing.convert_ty env p_out_ty in

    if List.length (fst (Type.decompose_funs out_ty)) >= 1 then
      begin
        let str_warning =
          Fmt.str "@[<v>name %s samples functions of type@;\
                  \  @[%a@]@;\
                   maybe you wanted to use a non-curryfied type instead?"
            (L.unloc s) Type.pp out_ty
        in
        Printer.prt `Warning "%s" str_warning
      end;
    
    let n_fty = Type.mk_ftype_tuple [] args_tys out_ty in

    List.iter2 (fun ty pty ->
        (* necessary to ensure that a term semantics is always a random variables
           (indeed, this guarantees that the set of tapes is finite, and can be
           equipped with the discrete sigma-algebra and the uniform distribution) *)
        if not (Symbols.TyInfo.is_finite table ty) then
          error (L.loc pty) KDecl (Failure "name can only be index by finite types")
      ) args_tys p_args_tys;

    let table, n =
      let data = Symbols.Name Symbols.{ n_fty } in
      Symbols.Name.declare ~approx:false table s ~data
    in
    Lemma.add_namelength_axiom table n n_fty, []

  | Decl.Decl_state decl ->
    parse_state_decl table decl, []

  | Decl.Decl_mutex decl ->
    let data = Mutex.MutexData decl.arity in
    let table, _ = Symbols.Mutex.declare ~approx:false table decl.name ~data in
    table, []

  | Decl.Decl_senc_w_join_hash (senc, sdec, h) ->
    Typing.declare_senc_joint_with_hash table senc sdec h, []

  | Decl.Decl_sign (sign, checksign, pk, tagi, ctys) ->
    let table = match tagi with
      | Some t -> define_oracle_tag_formula sign table t
      | None -> table in

    let ctys = parse_ctys table ctys ["m"; "sig"; "sk"; "pk"] in
    let m_ty     = List.assoc_opt "m"     ctys
    and sig_ty   = List.assoc_opt "sig"   ctys
    and sk_ty    = List.assoc_opt "sk"    ctys
    and pk_ty    = List.assoc_opt "pk"    ctys in

    Typing.declare_signature table
      ?m_ty ?sig_ty ?sk_ty ?pk_ty sign checksign pk,
    []

  | Decl.Decl_funs (kind,in_system,tyargs,decls) -> 
    parse_fun_decls table kind in_system tyargs decls

  | Decl.Decl_predicate decl -> parse_predicate_decl table decl, []

  | Decl.Decl_bty bty_decl ->
    let table, _ =
      let ty_infos = List.map Symbols.TyInfo.parse bty_decl.bty_infos in
      Symbols.BType.declare ~approx:false
        table
        bty_decl.bty_name
        ~data:(Symbols.TyInfo.Type ty_infos)
    in
    table, []

  | Decl.Decl_game game -> parse_game_decl (L.loc decl) table game, []

  | Decl.Tactic (id,ast) ->
    ProverTactics.register_macro (L.unloc id) ast ;
    table, []

  | Decl.Namespace_cmd cmd -> parse_namespace_cmd table cmd, []

let declare_list table decls =
  let table, subgs =
    List.map_fold (fun table d -> declare table d) table decls
  in
  table, List.flatten subgs

(*------------------------------------------------------------------*)
(** Check that [lem] applies to an unconstrained system variable [v]. *)
let local_stmt_valid_in_any_system (lem : Goal.local_statement) =
  match (lem.system.set :> SE.exposed).cnt with
  | Var v -> 
    let infos = List.assoc v lem.params.se_vars in
    infos = []
  | _ -> false

(*------------------------------------------------------------------*)
(** {3 Hints } *)

(*------------------------------------------------------------------*)
let add_hint_rewrite table (s : Symbols.p_path) =
  let lem = Lemma.find_stmt_local s table in
  let bound = lem.formula.bound in

  (* TODO: concrete: only support exact hint rather *)
  if bound <> None then
    Tactics.hard_failure ~loc:(L.loc (snd s))
      (Failure "rewrite hints must be asymptotic or exact");

  assert (lem.system.pair = None;); (* as we only forward [system.set] below *)

  Hint.add_hint_rewrite s lem.params lem.system.set lem.Goal.formula.formula table

(*------------------------------------------------------------------*)
let add_hint_smt table (s : Symbols.p_path) =
  let lem = Lemma.find_stmt_local s table in
  let bound = lem.formula.bound in

  (* TODO: concrete: only support exact hint rather *)
  if bound <> None && bound <> Some (Library.Real.mk_zero table) then
    Tactics.hard_failure ~loc:(L.loc (snd s))
      (Failure "smt hints must be asymptotic or exact");

  if not (local_stmt_valid_in_any_system lem) then
    Tactics.hard_failure ~loc:(Symbols.p_path_loc s)
      (Failure "smt hints must apply to any system");

  if lem.params.se_vars = [] then
    Tactics.hard_failure ~loc:(Symbols.p_path_loc s)
      (Failure "smt hints do not support system variables");

  Hint.add_hint_smt lem.Goal.formula.formula table

(*------------------------------------------------------------------*)
let deduction_hint_of_global_formula
    table loc (params : Params.t) (form : Equiv.form) : Hint.deduce_rule
  =
  let open Equiv in
  let failed error =
    Typing.error loc (Failure ("ill-formed deduction hint: " ^ error))
  in

  let uded = Library.Deduction.uniform_deduction table in

  let p = 
    match form with
    | Atom (Pred p) when p.psymb = uded -> p
    | _ -> failed ("must be a " ^ Symbols.path_to_string uded ^ " atom")
  in

  let system = as_seq1 p.se_args in

  (* [p.ty_args] starts by the type of the uniform argument to both
     [left] and [right]. 
     We extract it in [ty_args], possibly decomposing tuple arguments. *)
  let ty_arg = (List.hd p.ty_args) in
  let ty_args = Type.decompose_tuple ty_arg  in

  (* Get [left] and [right]. *)
  let left, right = 
    let _, pred_args = as_seq1 p.multi_args in
    as_seq2 pred_args
  in

  (* Apply them to the uniform arguments of the deduction property. *)
  let args = List.map (fun ty -> Vars.make_fresh ty "x") ty_args in
  let term_args = List.map Term.mk_var args in
  let left  = Term.mk_app ~simpl:true left  term_args in
  let right = Term.mk_app ~simpl:true right term_args in

  (* Try to decompose [right] as [(right | ∀ vars : cond)], which is
     sugar for [λ vars. (if cond then right else witness)]. *)
  let vars, right = 
    let vars, right = Term.decompose_fun right in
    let vars, subst = Term.refresh_vars vars in
    vars, Term.subst subst right     
  in
  let right, cond = 
    match Term.destr_app ~fs:Symbols.fs_ite ~arity:3 right with
    | Some [cond; t_then; Term.Fun (w, _)] 
      when   ( w = Library.Prelude.fs_witness && 
               not (Type.equal (Term.ty t_then) Type.tmessage) ) 
           || w = Symbols.fs_zero -> t_then, cond
    | _ -> right, Term.mk_true
  in

  { params; system; args; left; vars; right; cond; }

let add_hint_deduce table (s : Symbols.p_path) = 
  let lem = Lemma.find_stmt_global s table in

  let name = Symbols.p_path_to_string ~sep:"_" s in
  let rule = 
    deduction_hint_of_global_formula 
      table (Symbols.p_path_loc s) lem.params lem.formula
  in
  let h = Hint.{ name; cnt = rule; info = (); } in

  let ppe = default_ppe ~table () in
  Printer.prt `Result "@[<v 2>New deduction hint %a@]" 
    (Hint._pp_deduce_hint ppe) h;

  Hint.add_hint_deduce h table


(*------------------------------------------------------------------*)
let add_hint (table : Symbols.table) (h : Hint.p_hint) : Symbols.table =
  match h with
  | Hint.Hint_rewrite id -> add_hint_rewrite table id 
  | Hint.Hint_smt     id -> add_hint_smt     table id 
  | Hint.Hint_deduce  id -> add_hint_deduce  table id 
