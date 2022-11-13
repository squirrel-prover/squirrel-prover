open Utils

module S = System
module SE = SystemExpr

let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

let ty_out (table : Symbols.table) (ms : Symbols.macro) : Type.ty =
  match Symbols.Macro.get_def ms table with
    | Symbols.Global (_, ty) -> ty

    | Input | Output | Frame -> Type.tmessage

    | Cond | Exec -> Type.tboolean

    | Symbols.State (_,ty) -> ty

let ty_args (table : Symbols.table) (ms : Symbols.macro) : Type.ty list =
  match Symbols.Macro.get_def ms table with
    | Symbols.Global (arity, _) ->
      List.init arity (fun _ -> Type.tindex)

    | Input | Output | Frame | Cond | Exec -> []

    | Symbols.State (arity,_) ->
      List.init arity (fun _ -> Type.tindex)

let is_global table (ms : Symbols.macro) : bool =
  match Symbols.Macro.get_def ms table with
  | Symbols.Global (_, _) -> true
  | _ -> false

(*------------------------------------------------------------------*)
(** {2 Global macro definitions} *)

(** Data associated with global macro symbols.
    The definition of these macros is not naturally stored as part
    if action descriptions, but directly in the symbols table. *)
type global_data = {
  action : [`Strict | `Large] * Action.shape;
  (** The global macro is defined at any action which has
      the action shape as a strict or large prefix *)

  inputs : Vars.var list;
  (** Inputs of the macro, as variables, in order. *)

  indices : Vars.var list;
  (** Free indices of the macro, which corresponds to the prefix of
      the indices of the action defining the macro. *)
  (* TODO: ast_gen : clarify documentation *)

  ts : Vars.var;
  (** Free timestamp variable of the macro, which can only be instantiated
      by a strict suffix of [action]. *)

  bodies : (System.Single.t * Term.term) list;
  (** Definitions of macro body for single systems where it is defined. *)
}

let[@warning "-32"] pp fmt (g : global_data) : unit =
  let pp_strict fmt = function
    | `Strict -> Fmt.pf fmt "Strict"
    | `Large -> Fmt.pf fmt "Large"
  in
  Fmt.pf fmt "@[<v>action: @[%a@]@;\
              inputs: @[%a@]@;\
              indices: @[%a@]@;\
              ts: @[%a@]@;\
              @[<v 2>bodies:@;%a@]\
              @]%!"
    (Fmt.pair ~sep:Fmt.comma pp_strict Action.pp_shape) g.action
    Vars.pp_typed_list g.inputs
    Vars.pp_typed_list g.indices
    Vars.pp g.ts
    (Fmt.list ~sep:Fmt.cut
       (Fmt.parens (Fmt.pair ~sep:Fmt.comma System.Single.pp Term.pp)))
    g.bodies

(*------------------------------------------------------------------*)
type Symbols.data += Global_data of global_data

(*------------------------------------------------------------------*)
(** Get body of a global macro for a single system. *)
let get_single_body (single : S.Single.t) (data : global_data) : Term.term =
  try List.assoc single data.bodies with
  | Not_found -> Term.empty

(*------------------------------------------------------------------*)
(** Get body of a global macro for a system expression. *)
let get_body (system : SE.fset) (data : global_data) : Term.term =
  Term.combine
    (List.map
       (fun (lbl,single_system) -> lbl, get_single_body single_system data)
       (SE.to_list system))

(*------------------------------------------------------------------*)
(** Exported *)
let declare_global
      table system macro ~suffix ~action ~inputs ~indices ~ts body ty =
  assert (not (Type.is_tuni ty));
  let bodies =
    List.map
      (fun projection ->
         System.Single.make table system projection,
         Term.project1 projection body)
      (System.projections table system)
  in
  let data =
    Global_data
      {action = (suffix, action);
       inputs; indices; ts; bodies}
  in
  let def = Symbols.Global (List.length indices, ty) in
  Symbols.Macro.declare table macro ~data def

(*------------------------------------------------------------------*)
(** {2 Macro expansions} *)

let is_action = function Term.Action _ -> true | _ -> false
let get_action_symb = function Term.Action (a,_) -> a | _ -> assert false

let is_prefix strict a b =
  match Action.distance a b with
  | None -> false     (* [a] not prefix of [b] *)
  | Some i -> match strict with
    | `Large -> true
    | `Strict -> i > 0

(** Check is not done modulo equality.
    Not exported. *)
let is_defined (name : Symbols.macro) (a : Term.term) table =
  match Symbols.Macro.get_all name table with
    | Symbols.(Input | Output | Cond | State _), _ ->
      (* We can expand the definitions of input@A, output@A, cond@A and
         state@A when A is an action name. We cannot do so for a variable
         or a predecessor. *)
      is_action a

    | Symbols.(Exec | Frame), _ ->
      is_action a

    | Symbols.Global _, Global_data {action = (strict,a0) } ->
      (* We can only expand a global macro when [a0] is a prefix of [a],
       * because a global macro m(...)@A refer to inputs of A and
       * its sequential predecessors. *)
      if not (is_action a) then false
      else
        let asymb = get_action_symb a in
        let _, action = Action.get_def asymb table in
        is_prefix strict a0 (Action.get_shape action)

    | Symbols.Global _, _ -> assert false

(*------------------------------------------------------------------*)
(** Give the **internal** definition of a global macro. 
    Meaningless when working in a sequent. 
    Used for global rewriting, when rewriting in another global macro. *)
let get_def_glob_internal
    (table : Symbols.table) (system : SE.fset) 
    (symb : Term.msymb)  ~(args : Term.term list)
    ~(ts : Term.term) (inputs : Vars.vars)
  : Term.term 
  =
  assert (is_global table symb.s_symb);

  let data = 
    match Symbols.Macro.get_data symb.s_symb table with
    | Global_data data -> data 
    | _ -> assert false 
  in
  let body = get_body system data in
  let prefix_inputs = List.take (List.length data.inputs) inputs in
  let subst =
    List.map2
      (fun i i' -> Term.ESubst (Term.mk_var i, Term.mk_var i'))
      data.inputs prefix_inputs
    @
    List.map2
      (fun i t' -> Term.ESubst (Term.mk_var i, t'))
      data.indices args
  in
  let subst = Term.ESubst (Term.mk_var data.ts, ts) :: subst in
  Term.subst subst body

(*------------------------------------------------------------------*)
(** Give the definition of the global macro [symb(args)@ts]
    where [action] is the action corresponding to [ts].
    All prefixes of [action] must be valid actions of the system, except if:
    - [allow_dummy] is true
    - and for the full action, which may be dummy (we use [ts] instead). *)
let get_def_glob
   ~(allow_dummy : bool)
    (system : SE.fset)
    (table  : Symbols.table)
    (_symb  : Term.msymb)
    ~(args  : Term.term list)
    ~(ts    : Term.term)
    (action : Action.action)
    (data   : global_data)
  : Term.term
  =
  assert (List.length data.inputs <= List.length action) ;
  let idx_subst =
    List.map2
      (fun i t -> Term.ESubst (Term.mk_var i, t))
      data.indices
      args
  in
  let ts_subst = Term.ESubst (Term.mk_var data.ts, ts) in
  (* Compute the relevant part of the action, i.e. the
     prefix of length [length inputs], reversed. *)
  let rev_action =
    let rec drop n l = if n=0 then l else drop (n-1) (List.tl l) in
    drop (List.length action - List.length data.inputs) (List.rev action)
  in
  let subst,_ =
    List.fold_left
      (fun (subst,action_prefix) x ->
         let a_ts =
           if List.length rev_action = List.length action_prefix &&
              allow_dummy
           then ts
           else SE.action_to_term table system (List.rev action_prefix)
         in
         let in_tm = Term.mk_macro Term.in_macro [] a_ts in
         Term.ESubst (Term.mk_var x, in_tm) :: subst,
         List.tl action_prefix)
      (ts_subst :: idx_subst, rev_action)
      data.inputs
  in

  let t = Term.subst subst (get_body system data) in
  Term.simple_bi_term t 

(*------------------------------------------------------------------*)
(** Exported *)

let get_definition_nocntxt
    (system : SE.fset)
    (table  : Symbols.table)
    (symb   : Term.msymb)
    ~(args  : Term.term list)
    (asymb  : Symbols.action)
    (aidx   : Term.term list) : [ `Def of Term.term | `Undef ]
  =
  let init_or_generic init_case f =
    `Def (if asymb = Symbols.init_action
          then init_case
          else f (Term.mk_action asymb aidx))
  in
  let action = Action.of_term asymb aidx table in

  (* we do not apply the substitution right away, as it may fail by
     trying to substitute indices by non-variable terms. *)
  let unapplied_descr, descr_subst =
    SE.descr_of_action table system action
  in
  match Symbols.Macro.get_all symb.s_symb table with
  | Symbols.Input, _ ->
    init_or_generic Term.empty (fun a ->
        Term.mk_fun table Symbols.fs_att 
          [Term.mk_macro Term.frame_macro [] (Term.mk_pred a)])

  | Symbols.Output, _ ->
    `Def (Term.subst descr_subst (snd unapplied_descr.output))

  | Symbols.Cond, _ ->
    `Def (Term.subst descr_subst (snd unapplied_descr.condition))

  | Symbols.Exec, _ ->
    init_or_generic Term.mk_true (fun a ->
        Term.mk_and
          (Term.mk_macro symb [] (Term.mk_pred a))
          (Term.mk_macro Term.cond_macro [] a))

  | Symbols.Frame, _ ->
    init_or_generic Term.mk_zero (fun a ->
        Term.mk_pair
          (Term.mk_macro symb [] (Term.mk_pred a))
          (Term.mk_pair
             (Term.mk_of_bool (Term.mk_macro Term.exec_macro [] a))
             (Term.mk_ite
                (Term.mk_macro Term.exec_macro [] a)
                (Term.mk_macro Term.out_macro [] a)
                Term.mk_zero)))

  | Symbols.State _, _ ->
    `Def begin
      let descr_updates =
        List.map (fun (ss,args,t) ->
            ss, Term.subst_vars descr_subst args, Term.subst descr_subst t
          ) unapplied_descr.updates
      in
      try
        (* Look for an update of the state macro [name] in the updates
           of [action]; we rely on the fact that [action] can only contain
           a single update for each state macro symbol *)
        let (_ns, ns_args, msg) : Symbols.macro * Vars.vars * Term.term =
          List.find (fun (ns,ns_args,_) ->
              ns = symb.s_symb &&
              List.length ns_args = List.length args
            ) descr_updates
        in

        (* Init case: we substitute the indices by their definition. *)
        if asymb = Symbols.init_action then
          let s = List.map2 (fun i1 i2 ->
              Term.ESubst (Term.mk_var i1, i2)
            ) ns_args args
          in
          Term.subst s msg

        (* If indices [args] of the macro we want to expand
           are equal to indices [ns_args] corresponding to this macro
           in the action description, then the macro is expanded as defined
           by the update term. *)
        else if args = Term.mk_vars ns_args then
          msg

        (* Otherwise, we need to take into account the possibility that
           [arg] and [ns_args] might be equal, and generate a conditional.  *)
        else
          let ns_args : Term.terms = Term.mk_vars ns_args in
          let def =
            Term.mk_ite
              (Term.mk_eqs ~simpl:true args ns_args)
              msg
              (Term.mk_macro symb args (Term.mk_pred (Term.mk_action asymb aidx))) 
          in
          def
      with Not_found ->
        Term.mk_macro symb args (Term.mk_pred (Term.mk_action asymb aidx))
    end

  | Symbols.Global _,
    Global_data ({action = (strict, glob_a)} as global_data ) ->
    if is_prefix strict glob_a (Action.get_shape action)
    then `Def (get_def_glob ~allow_dummy:false system table
                 symb ~args ~ts:(Term.mk_action asymb aidx) action global_data)
    else `Undef

  |  _ -> assert false

(*------------------------------------------------------------------*)
type def_result = [ `Def of Term.term | `Undef | `MaybeDef ]

(** See [.mli] *)
type expand_context = InSequent | InGlobal of { inputs : Vars.vars }

(** Not exported *)
let get_definition_in_sequent
    (cntxt : Constr.trace_cntxt)
    (symb  : Term.msymb)
    ~(args : Term.term list)
    ~(ts   : Term.term)
  : def_result
  =
  match SE.to_fset cntxt.system with
  | exception SE.(Error Expected_fset) -> `MaybeDef
  | system ->
    (* Try to find an action equal to [ts] in [cntxt]. *)
    let ts_action =
      if is_defined symb.s_symb ts cntxt.table
      then ts
      else
        omap_dflt ts (fun models ->
            odflt ts (Constr.find_eq_action models ts)
          ) cntxt.models
    in
    match ts_action with
    | Term.Action (asymb, idx) -> begin
        match get_definition_nocntxt system cntxt.table symb ~args asymb idx with
        | `Undef    -> `Undef
        | `Def mdef -> `Def (Term.subst [Term.ESubst (ts_action, ts)] mdef)
      end
    | _ -> `MaybeDef

  (*------------------------------------------------------------------*)
(** Exported *)
let get_definition
    ?(mode : expand_context = InSequent)
    (cntxt : Constr.trace_cntxt)
    (symb  : Term.msymb)
    ~(args : Term.term list)
    ~(ts   : Term.term)
  : def_result
  =
  (* first try to get the definition as in a sequent. *)
  match get_definition_in_sequent cntxt symb ~args ~ts, mode with 
  | `MaybeDef, InGlobal { inputs } 
    when is_global cntxt.table symb.Term.s_symb -> 
    (* if that fails, and if we are in [InGlobal] mode, get the internal def. *)
    `Def (get_def_glob_internal cntxt.table cntxt.system symb ~args ~ts inputs)
  | res, _ -> res

(** Exported *)
let get_definition_exn
    ?(mode : expand_context = InSequent)
    (cntxt : Constr.trace_cntxt)
    (symb  : Term.msymb)
    ~(args : Term.term list)
    ~(ts    : Term.term) : Term.term
  =
  match get_definition ~mode cntxt symb ~args ~ts with
  | `Undef ->
    soft_failure (Failure "cannot expand this macro: macro is undefined");

  | `MaybeDef ->
    soft_failure (Failure "cannot expand this macro: undetermined action")

  | `Def mdef -> mdef


(*------------------------------------------------------------------*)
(** Exported *)
let get_dummy_definition
    (table  : Symbols.table)
    (system : SE.fset)
    (symb   : Term.msymb)
    ~(args : Term.term list)
  : Term.term
  =
  match Symbols.Macro.get_all symb.s_symb table with
  | Symbols.Global _,
    Global_data ({action = (strict,action)} as gdata) ->
    (* [dummy_action] is a dummy strict suffix of [action]. *)
    let dummy_action =
      let prefix = Action.dummy action in
      match strict with
      | `Large -> prefix
      | `Strict ->
        let dummy_end  =
          Action.{ par_choice = 0,[] ; sum_choice = 0,[] }
        in
        prefix @ [dummy_end]
    in

    let tvar = Vars.make_fresh Type.Timestamp "dummy" in
    let ts = Term.mk_var tvar in

    get_def_glob ~allow_dummy:true
      system table symb ~args ~ts dummy_action gdata

  | _ -> assert false

(*------------------------------------------------------------------*)
type system_map_arg =
  | ADescr  of Action.descr 
  | AGlobal of { is : Vars.vars; ts : Vars.var; 
                 ac_descrs : Action.descr list; inputs : Vars.vars }

(*------------------------------------------------------------------*)
(** Given the name [ns] of a macro as well as a function [f] over
    terms, an [old_single_system] and a [new_single_system], takes the
    existing definition of [ns] in the old system, applies [f] to the
    existing definition, and update the value of [ns] accordingly in
    the new system. *)
let update_global_data
    (table      : Symbols.table)
    (ms         : Symbols.macro)
    (dec_def    : Symbols.macro_def)
    (old_system : System.Single.t)
    (new_system : System.Single.t)
    (func       : 
       (system_map_arg ->
        Symbols.macro -> 
        Term.term -> 
        Term.term))
  : Symbols.table
  =
  match Symbols.Macro.get_data ms table with
  | Global_data data when List.mem_assoc old_system data.bodies ->
    assert (not (List.mem_assoc new_system data.bodies));
    let body = 
      (* old body *)
      let body = get_single_body old_system data in
      (* find all actions in the old system that have a shape where
         the macro is defined *)
      let actions_map = System.descrs table old_system.system in
      let strict, prefix_shape = data.action in
      let possible_actions = 
        S.Msh.fold
          (fun shape act acs->
            let right_shape = is_prefix strict prefix_shape shape in
            if right_shape then act::acs else acs)
        actions_map
        []
      in
      let aglob = AGlobal { 
          is = data.indices; 
          ts = data.ts; 
          ac_descrs = possible_actions;
          inputs = data.inputs ;
        } in
      func aglob ms body 
    in
    let data =
      Global_data { data with
                    bodies = (new_system, body) :: data.bodies }
    in
    Symbols.Macro.redefine table ~data ms dec_def

  | _ -> table

  
