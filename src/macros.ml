open Utils

module SE = SystemExpr

let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** {2 Macro definitions} *)

type global_data = {
  action  : [`Strict | `Large] * Action.shape;
  (** the global macro is defined at any action which is a strict or large
      suffix of [action]  *)

  inputs  : Vars.var list;
  (** inputs of the macro, as variables, in order *)

  indices : Vars.var list;
  (** free indices of the macro, which corresponds to the prefix of
      the indices of the action defining the macro *)

  ts      : Vars.var;
  (** free timestamp variable of the macro, which can only be instantiated
      by a strict suffix of [action] *)

  default_body    : Term.term;
  (** macro body shared by all systems *)

  systems_body    : (SE.single_system * Term.term) list;
  (** Optional alternative definitions of the body for a given system.
      Used by System modifiers.
  *)

}

type Symbols.data += Global_data of global_data


let sproj s t = Term.pi_term ~projection:(SE.get_proj s) t

let get_single_body single_system data =
  let body = try
      (List.assoc single_system data.systems_body)
    with Not_found ->  data.default_body
  in
  sproj single_system body

let get_body system data : Term.term =
  let get_pair_body s1 s2 =
    match List.assoc s1 data.systems_body with
    | b1 ->
      let b1 = sproj s1 b1 in
      begin
        match List.assoc s2 data.systems_body with
        | b2 -> Term.mk_diff b1 (sproj s2 b2)
        | exception Not_found -> Term.mk_diff b1 (sproj s2 data.default_body)
        end
    | exception Not_found -> begin
        match List.assoc s2 data.systems_body with
        | b2 -> Term.mk_diff (sproj s1 data.default_body) (sproj s2 b2)
        | exception Not_found ->
          let t1, t2 = sproj s1 data.default_body, sproj s2 data.default_body in
          if t1 = t2 then t1 else Term.mk_diff t1 t2
        end
  in
  match system with
  | SE.Single s      -> get_single_body s data
  | SE.SimplePair s  -> get_pair_body (SE.Left s) (SE.Right s)
  | SE.Pair (s1, s2) -> get_pair_body s1 s2
  | SE.Empty         -> assert false (* FIXME: user-level exception? *)

(** Exported *)
let apply_global_data table ns dec_def old_single_system new_single_system data f =
  match Symbols.Macro.get_data ns table with
  | Global_data data ->
    let body = get_single_body old_single_system data in
    let data = Global_data {data with systems_body = (new_single_system, f body)
                                                     ::data.systems_body} in
    Symbols.Macro.redefine table ~data ns dec_def
  | _ -> table

let is_tuni = function Type.TUnivar _ -> true | _ -> false

(** Exported *)
let declare_global table name ~suffix ~action ~inputs ~indices ~ts body ty =
  assert (not (is_tuni ty));
  let data =
    Global_data
      {action = (suffix, action);
       inputs; indices; ts; default_body=body; systems_body = []}
  in
  let def = Symbols.Global (List.length indices, ty) in
  Symbols.Macro.declare table name ~data def

(*------------------------------------------------------------------*)
(** {2 Macro expansions} *)

let is_action = function Term.Action _ -> true | _ -> false
let get_action_symb = function Term.Action (a,_) -> a | _ -> assert false

let is_prefix strict a b =
  match Action.distance a b with
  | None -> false     (* [a] and [b] incomparable *)
  | Some i -> match strict with
    | `Large -> true
    | `Strict -> i > 0

(** Check is not done module equality.
    Not exported. *)
let is_defined name a table =
  match Symbols.Macro.get_all name table with
    | Symbols.(Input | Output | Cond | State _), _ ->
      (* We can expand the definitions of input@A, output@A, cond@A and
         state@A when A is an action name. We cannot do so for a variable
         or a predecessor. *)
      is_action a

    | Symbols.(Exec | Frame), _ ->
      is_action a

    | Symbols.Global _, Global_data {action = (strict,a0); inputs } ->
      (* We can only expand a global macro when [a0] is a prefix of [a],
       * because a global macro m(...)@A refer to inputs of A and
       * its sequential predecessors. *)
      if not (is_action a) then false
      else
        let asymb = get_action_symb a in
        let _, action = Action.of_symbol asymb table in
        is_prefix strict a0 (Action.get_shape action)

    | Symbols.Global _, _ -> assert false

(*------------------------------------------------------------------*)
type def_result = [ `Def of Term.term | `Undef | `MaybeDef ]

(** give the definition of the global macro [symb] at timestamp [a]
    corresponding to action [action]
    All prefix of [action] must be valid actions of the system, except if:
    - [allow_dummy] is true
    - and for the full action, which may be dummy (we use [a] instead) *)
let get_def_glob
    ~(allow_dummy : bool)
    (system : SE.t)
    (table  : Symbols.table)
    (symb   : Term.msymb)
    (a      : Term.term)
    (action : Action.action)
    (data   : global_data) 
  : def_result
  =
  assert (List.length data.inputs <= List.length action) ;
  let idx_subst =
    List.map2
      (fun i i' -> Term.ESubst (Term.mk_var i,Term.mk_var i'))
      data.indices
      symb.s_indices
  in
  let ts_subst = Term.ESubst (Term.mk_var data.ts, a) in
  (* Compute the relevant part of the action, i.e. the
       * prefix of length [length inputs], reversed. *)
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
           then a
           else SE.action_to_term table system (List.rev action_prefix)
         in
         let in_tm =
           Term.mk_macro Term.in_macro [] a_ts
         in
         Term.ESubst (Term.mk_var x,in_tm) :: subst,
         List.tl action_prefix)
      (ts_subst::idx_subst,rev_action)
      data.inputs
  in

  let t = Term.subst subst (get_body system data) in
  `Def (Term.simple_bi_term t)

(*------------------------------------------------------------------*)
(** Exported *)

let get_definition_nocntxt
    (system : SE.t)
    (table  : Symbols.table)
    (symb   : Term.msymb)
    (a      : Term.term) : [ `Def of Term.term | `Undef | `MaybeDef ]
  =
  match Symbols.Macro.get_all symb.s_symb table with
  | Symbols.Input, _ ->
    begin match a with
      | Term.Action (s,_) when s = Symbols.init_action -> `Def Term.empty
      | Term.Action _ ->
        let d =
          Term.mk_fun table Symbols.fs_att []
            [Term.mk_macro Term.frame_macro [] (Term.mk_pred a)]
        in
        `Def d
      | _ -> `MaybeDef
    end

  | Symbols.Output, _ ->
    let symb, indices = oget (Term.destr_action a) in
    let action = Action.of_term symb indices table in
    let descr =
      SE.descr_of_action table system action
    in
    `Def (snd descr.Action.output)

  | Symbols.Cond, _ ->
    let symb, indices = oget (Term.destr_action a) in
    let action = Action.of_term symb indices table in
    let descr =
      SE.descr_of_action table system action
    in
    `Def (snd Action.(descr.condition))

  | Symbols.Exec, _ ->
    begin match a with
      | Term.Action (s,_) when s = Symbols.init_action -> `Def Term.mk_true
      | Term.Action _ ->
        let d =
          Term.mk_and
            (Term.mk_macro symb [] (Term.mk_pred a))
            (Term.mk_macro Term.cond_macro [] a)
        in
        `Def d
      | _ -> `MaybeDef
    end

  | Symbols.Frame, _ ->
    begin match a with
      | Term.Action (s,_) when s = Symbols.init_action -> `Def Term.mk_zero
      | Term.Action _ ->
        let def =
          Term.mk_pair
            (Term.mk_macro symb [] (Term.mk_pred a))
            (Term.mk_pair
               (Term.mk_of_bool (Term.mk_macro Term.exec_macro [] a))
               (Term.mk_ite
                  (Term.mk_macro Term.exec_macro [] a)
                  (Term.mk_macro Term.out_macro [] a)
                  Term.mk_zero))
        in
        `Def def
      | _ -> `MaybeDef
    end

  | Symbols.State _, _ ->
    let asymb, indices = oget (Term.destr_action a) in
    let action = Action.of_term asymb indices table in
    let descr = SE.descr_of_action table system action in
    begin try
        (* Look for an update of the state macro [name] in the updates
           of [action]; we rely on the fact that [action] can only contain
           a single update for each state macro symbol *)
        let (ns, msg) : Term.state * Term.term =
          List.find (fun (ns,_) ->
              ns.Term.s_symb = symb.s_symb &&
              List.length ns.Term.s_indices = List.length symb.s_indices
            ) descr.Action.updates
        in
        assert (ns.Term.s_typ = symb.s_typ);

        (* init case: we substitute the indices by their definition *)
        if a = Term.init then
          let s = List.map2 (fun i1 i2 ->
              Term.ESubst (Term.mk_var i1, Term.mk_var i2)
              ) ns.s_indices symb.s_indices
          in
          `Def (Term.subst s msg)
          (* if indices [args] of the macro we want
             to expand are equal to indices [is] corresponding to this macro
             in the action description, then the macro expanded as defined
             by the update term *)
        else if symb.s_indices = ns.s_indices then `Def msg
        (*  otherwise, we need to take into account the possibility that
            [arg] and [is] might be equal, and generate a conditional.  *)
        else
          let def =
            Term.mk_ite
              (Term.mk_indices_eq symb.s_indices ns.s_indices)
              msg
              (Term.mk_macro symb [] (Term.mk_pred a))
          in
          `Def def
      with Not_found ->
        `Def (Term.mk_macro symb [] (Term.mk_pred a))
    end

  | Symbols.Global _,
    Global_data ({action = (strict, glob_a)} as global_data ) ->
    if not (is_action a) then `MaybeDef
    else
      let tsymb, tidx = oget (Term.destr_action a) in
      let action = Action.of_term tsymb tidx table in
      if not (is_prefix strict glob_a (Action.get_shape action)) then
        `Undef
      else
        get_def_glob ~allow_dummy:false system table symb a action global_data

  |  _ -> assert false

let get_definition
    (cntxt : Constr.trace_cntxt)
    (symb  : Term.msymb)
    (ts    : Term.term) 
  : def_result
  =
  (* try to find an action equal to [ts] in [cntxt] *)
  let ts_action =
    if is_defined symb.s_symb ts cntxt.table
    then ts
    else
      omap_dflt ts (fun models ->
          odflt ts (Constr.find_eq_action models ts)
        ) cntxt.models
  in
  if not (is_defined symb.s_symb ts_action cntxt.table) then `Undef else
    match get_definition_nocntxt cntxt.system cntxt.table symb ts_action with
    | `Undef | `MaybeDef as res -> res
    | `Def mdef ->
      let mdef = Term.subst [Term.ESubst (ts_action, ts)] mdef in
      `Def (mdef)

let get_definition_exn
    (cntxt : Constr.trace_cntxt)
    (symb  : Term.msymb)
    (ts    : Term.term) : Term.term
  =
  match get_definition cntxt symb ts with
  | `Undef ->
    soft_failure (Failure "cannot expand this macro: macro is undefined");

  | `MaybeDef ->
    soft_failure (Failure "cannot expand this macro: undetermined action")

  | `Def mdef -> mdef


(*------------------------------------------------------------------*)
(** Exported *)
let get_dummy_definition
    (table  : Symbols.table)
    (system : SE.t)
    (symb   : Term.msymb) 
  : Term.term
  =
  match Symbols.Macro.get_all symb.s_symb table with
  | Symbols.Global _,
    Global_data ({action = (strict,action); inputs} as gdata) ->
    (* [dummy_action] is a dummy strict suffix of [action] *)
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

    let tvar = Vars.make_new Type.Timestamp "dummy" in
    let ts = Term.mk_var tvar in

    let def =
      get_def_glob ~allow_dummy:true system table symb ts dummy_action gdata
    in
    begin
      match def with
      | `Def def -> def
      | _ -> assert false
    end
  | _ -> assert false
