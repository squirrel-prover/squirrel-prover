open Utils

module S = System
module SE = SystemExpr

let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** {2 Utilities} *)
 
let ty_out (table : Symbols.table) (ms : Symbols.macro) : Type.ty =
  match Symbols.get_macro_data ms table with
    | Symbols.Global (_, ty, _) -> ty

    | Input | Output | Frame -> Type.tmessage

    | Cond | Exec -> Type.tboolean

    | Symbols.State (_,ty,_) -> ty

let ty_args (table : Symbols.table) (ms : Symbols.macro) : Type.ty list =
  match Symbols.get_macro_data ms table with
    | Symbols.Global (arity, _, _) ->
      List.init arity (fun _ -> Type.tindex)

    | Input | Output | Frame | Cond | Exec -> []

    | Symbols.State (arity,_,_) ->
      List.init arity (fun _ -> Type.tindex)

let is_global table (ms : Symbols.macro) : bool =
  match Symbols.get_macro_data ms table with
  | Symbols.Global (_, _, _) -> true
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
  (* FIXME: clarify documentation *)

  ts : Vars.var;
  (** Free timestamp variable of the macro, which can only be instantiated
      by a strict suffix of [action]. *)

  bodies : (System.Single.t * Term.term) list;
  (** Definitions of macro body for single systems where it is defined. *)

  ty : Type.ty;
  (** The type of the macro, which does not depends on the system. *)
}

(*------------------------------------------------------------------*)
type Symbols.global_macro_def += Global_data of global_data

let data_of_global_data (d : global_data) : Symbols.data =
  Symbols.Macro (Global (List.length d.indices, d.ty, Global_data d))

(*------------------------------------------------------------------*)
let pp fmt (g : global_data) : unit =
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
let get_global_data : Symbols.global_macro_def -> global_data = function
  | Global_data g -> g
  | _ -> assert false
    
let as_global_macro : Symbols.data -> global_data = function
  | Symbols.Macro (Global (_, _, g)) -> get_global_data g
  | _ -> assert false

(*------------------------------------------------------------------*)
(** Get body of a global macro for a single system. *)
let get_single_body table (single : S.Single.t) (data : global_data) : Term.term =
  try List.assoc single data.bodies with
  | Not_found -> Term.Prelude.mk_witness table ~ty_arg:data.ty
  (* undefined macros default to witness *)

(*------------------------------------------------------------------*)
(** Get body of a global macro for a system expression. *)
let get_body table (system : SE.fset) (data : global_data) : Term.term =
  Term.combine
    (List.map
       (fun (lbl,single_system) -> lbl, get_single_body table single_system data)
       (SE.to_list system))

(*------------------------------------------------------------------*)
(** Exported *)
let declare_global
    table system macro ~suffix ~action ~inputs ~indices ~ts body ty
    : Symbols.table * Symbols.macro
  =
  assert (not (Type.contains_tuni ty));
  let bodies =
    List.map
      (fun projection ->
         System.Single.make table system projection,
         Term.project1 projection body)
      (System.projections table system)
  in
  let glob_data =
    {action = (suffix, action); inputs; indices; ts; bodies; ty}
  in  
  let data = data_of_global_data glob_data in
  Symbols.Macro.declare ~approx:true table macro ~data 

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
  match Symbols.get_macro_data name table with
  | Input | Output | Cond | State _ ->
    (* We can expand the definitions of input@A, output@A, cond@A and
       state@A when A is an action name. We cannot do so for a variable
       or a predecessor. *)
    is_action a

  | Exec | Frame -> is_action a

  | Global (_, _, Global_data {action = (strict,a0) }) ->
    (* We can only expand a global macro when [a0] is a prefix of [a],
     * because a global macro m(...)@A refer to inputs of A and
     * its sequential predecessors. *)
    if not (is_action a) then false
    else
      let asymb = get_action_symb a in
      let _, action = Action.get_def asymb table in
      is_prefix strict a0 (Action.get_shape action)

  | Global _ -> assert false    (* impossible *)

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

  let data = as_global_macro (Symbols.Macro.get_data symb.s_symb table) in
  let body = get_body table system data in
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

  let t = Term.subst subst (get_body table system data) in
  Term.simple_bi_term (SE.to_projs system) t

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
  match Symbols.get_macro_data symb.s_symb table with
  | Input ->
    init_or_generic Term.empty
      (fun a ->
         Term.mk_fun table Symbols.fs_att 
           [Term.mk_macro Term.frame_macro [] (Term.mk_pred a)])

  | Output ->
    `Def (Term.subst descr_subst (snd unapplied_descr.output))

  | Cond ->
    `Def (Term.subst descr_subst (snd unapplied_descr.condition))

  | Exec ->
    init_or_generic Term.mk_true (fun a ->
        Term.mk_and
          (Term.mk_macro symb [] (Term.mk_pred a))
          (Term.mk_macro Term.cond_macro [] a))

  | Frame ->
    init_or_generic Term.mk_zero (fun a ->
        Term.mk_pair
          (Term.mk_macro symb [] (Term.mk_pred a))
          (Term.mk_pair
             (Term.mk_of_bool (Term.mk_macro Term.exec_macro [] a))
             (Term.mk_ite
                (Term.mk_macro Term.exec_macro [] a)
                (Term.mk_macro Term.out_macro [] a)
                Term.mk_zero)))

  | State _ ->
    `Def begin
      try
        (* Look for an update of the state macro [name] in the updates
           of [action]; we rely on the fact that [action] can only contain
           a single update for each state macro symbol *)
        let (ns_args, msg) : Term.terms * Term.term =
          let _, ns_args, msg =
            List.find (fun (ns,ns_args,_) ->
                ns = symb.s_symb &&
                List.length ns_args = List.length args
              ) unapplied_descr.updates
          in
          List.map (Term.subst descr_subst) ns_args, Term.subst descr_subst msg
        in

        (* Init case: we substitute the indices by their definition. *)
        if asymb = Symbols.init_action then
          let s = List.map2 (fun i1 i2 ->
              match i1 with
              | Term.Var _ -> Term.ESubst (i1, i2)
              | _ -> assert false
              (* impossible for well-formed action description for init *)
            ) ns_args args
          in
          Term.subst s msg

        (* If indices [args] of the macro we want to expand
           are equal to indices [ns_args] corresponding to this macro
           in the action description, then the macro is expanded as defined
           by the update term. *)
        else if List.for_all2 Term.equal args ns_args then
          msg

        (* Otherwise, we need to take into account the possibility that
           [arg] and [ns_args] might be equal, and generate a conditional.  *)
        else
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

  | Global (_,_,gdata) ->
    let {action = (strict, glob_a)} as gdata = get_global_data gdata in
    if is_prefix strict glob_a (Action.get_shape action)
    then `Def (get_def_glob ~allow_dummy:false system table
                 symb ~args ~ts:(Term.mk_action asymb aidx) action gdata)
    else `Undef

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
  | exception SE.(Error (_,Expected_fset)) -> `MaybeDef
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
  let { action = strict,action; } as gdata =
    as_global_macro (Symbols.Macro.get_data symb.s_symb table)
  in
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
    (old_system : System.Single.t)
    (new_system : System.Single.t)
    (func       : 
       (system_map_arg ->
        Symbols.macro -> 
        Term.term -> 
        Term.term))
  : Symbols.table
  =
  if not (is_global table ms) then table
  else
    let data = Symbols.Macro.get_data ms table in
    let gdata = as_global_macro data in
    if not (List.mem_assoc old_system gdata.bodies) then table
    else
      begin
        assert (not (List.mem_assoc new_system gdata.bodies));
        let body = 
          (* old body *)
          let body = get_single_body table old_system gdata in
          (* find all actions in the old system that have a shape where
             the macro is defined *)
          let actions_map = System.descrs table old_system.system in
          let strict, prefix_shape = gdata.action in
          let possible_actions = 
            S.Msh.fold
              (fun shape act acs->
                 let right_shape = is_prefix strict prefix_shape shape in
                 if right_shape then act::acs else acs)
              actions_map
              []
          in
          let aglob = AGlobal { 
              is = gdata.indices; 
              ts = gdata.ts; 
              ac_descrs = possible_actions;
              inputs = gdata.inputs ;
            } in
          func aglob ms body 
        in
        let data =
          data_of_global_data { gdata with bodies = (new_system, body) :: gdata.bodies }
        in
        Symbols.Macro.redefine table ~data ms 
      end

