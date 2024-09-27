open Utils
open Ppenv

module L = Location
module S = System
module SE = SystemExpr

(*------------------------------------------------------------------*)
(** {2 Macro for mutable state} *)

type Symbols.state_macro_def += StateInit_data of Vars.var list * Term.term

let get_init_states table : (Symbols.macro * Term.terms * Term.term) list =
  Symbols.Macro.fold (fun s data acc ->
      match data with
      | Symbols.Macro (State (_arity,kind,StateInit_data (l,t))) ->
        assert (Type.equal kind (Term.ty t));
        (s,List.map Term.mk_var l,t) :: acc
      | _ -> acc
    ) [] table

(*------------------------------------------------------------------*)
(** {2 General macro definitions} *)
    
(*------------------------------------------------------------------*)
(** A definition of a general structured recursive macro definition:
    [m = λτ ↦ if not (happens τ) then default
              else if τ = init then tinit
              else body τ] *)
type structed_macro_data = {
  name    : Symbols.macro;        (** a macro [m] *)
  default : Term.term;            (** [m@τ] if not [happens(τ)] *)
  tinit   : Term.term;            (** [m@init] *)
  body    : Vars.var * Term.term; (** [λτ. m@τ] when [happens(τ) ∧ τ≠init] *)
  rec_ty  : Type.ty;              (** The type of [τ] *)
  ty      : Type.ty;              (** The type of the **body** of [m] *)
}

(** A general macro definition. *)
(* FIXME: quantum: move all macro definitions in this type *)
type general_macro_data = 
  | Structured of structed_macro_data
  | ProtocolMacro of [`Output | `Cond] 
  (** ad hoc macro definitions using action descriptions *)

type Symbols.general_macro_def += Macro_data of general_macro_data

let get_general_macro_data : Symbols.general_macro_def -> general_macro_data = function
    | Macro_data g -> g
    | _ -> assert false
    
let as_general_macro : Symbols.data -> general_macro_data = function
  | Symbols.Macro (General g) -> get_general_macro_data g 
  | _ -> assert false

(*------------------------------------------------------------------*)
(** {2 Execution models} *)
    
type exec_model_def = {
  np : Symbols.npath;
  (** namespace where this execution model will define its macros *)

  input_name : Symbols.macro;
  (** input macro in this execution model *)

  output_name : Symbols.macro;
  (** output macro in this execution model *)

  cond_name : Symbols.macro;
  (** condition macro in this execution model *)

  rec_ty : Type.ty;
  (** type along which the execution takes place (actions, integers, ...) *)
  
  macros : (Symbols.macro * general_macro_data) list
  (** definitions of the execution model macros *)
}

(*------------------------------------------------------------------*)
(** {3 Builtin execution models} *)

(** An execution model *)
type exec_model = Classical | PostQuantum

(*------------------------------------------------------------------*)
module Classical = struct
  let model _table =
    let ts_v = Vars.mk (Ident.create "τ") Type.ttimestamp in
    let ts   = Term.mk_var ts_v in

    (*------------------------------------------------------------------*)
    let frame =
      let body =
        Term.mk_pair
          (Term.mk_macro Term.frame_macro [] (Term.mk_pred ts))
          (Term.mk_pair
             (Term.mk_of_bool (Term.mk_macro Term.exec_macro [] ts))
             (Term.mk_ite
                (Term.mk_macro Term.exec_macro [] ts)
                (Term.mk_macro Term.out_macro [] ts)
                Term.mk_zero))
      in 
      Structured {
        name    = Symbols.frame;
        default = Term.empty;
        tinit   = Term.mk_zero;
        body    = (ts_v, body);
        rec_ty  = Type.ttimestamp;
        ty      = Type.tmessage;
      }
    in

    (*------------------------------------------------------------------*)
    let input =
      let body =
        Term.mk_fun0
          Symbols.fs_att { fty = Symbols.ftype_builtin Symbols.fs_att; ty_args = [] }
          [Term.mk_macro Term.frame_macro [] (Term.mk_pred ts)]
      in 
      Structured {
        name    = Symbols.inp;
        default = Term.empty;
        tinit   = Term.empty;
        body    = (ts_v, body);
        rec_ty  = Type.ttimestamp;
        ty      = Type.tmessage;
      }
    in

    (*------------------------------------------------------------------*)
    let exec =
      let body =
        Term.mk_and
          (Term.mk_macro Term.exec_macro [] (Term.mk_pred ts))
          (Term.mk_macro Term.cond_macro [] ts)
      in 
      Structured {
        name    = Symbols.exec;
        default = Term.mk_false;
        tinit   = Term.mk_true;
        body    = (ts_v, body);
        rec_ty  = Type.ttimestamp;
        ty      = Type.tboolean;
      }
    in

    (*------------------------------------------------------------------*)
    let output = ProtocolMacro `Output in
    let cond   = ProtocolMacro `Cond   in

    (*------------------------------------------------------------------*)
    {
      np          = Symbols.top_npath;
      rec_ty      = Type.ttimestamp;
      input_name  = Symbols.inp;
      output_name = Symbols.out;
      cond_name   = Symbols.cond;
      macros      = [Symbols.frame, frame ;
                     Symbols.inp  , input ;
                     Symbols.exec , exec  ;
                     Symbols.out  , output;
                     Symbols.cond , cond  ; ];
    } 
end (* Classical *)

(*------------------------------------------------------------------*)
module PostQuantum = struct
  let model table =
    let ts_v = Vars.mk (Ident.create "τ") Type.ttimestamp in
    let ts   = Term.mk_var ts_v in
    
    let qwitness = Library.Prelude.mk_witness table ~ty_arg:(Type.tquantum_message) in

    (*------------------------------------------------------------------*)
    let frame =
      let body =
        Term.mk_pair
          (Term.mk_macro Term.q_frame_macro [] (Term.mk_pred ts))
          (Term.mk_pair
             (Term.mk_of_bool (Term.mk_macro Term.q_exec_macro [] ts))
             (Term.mk_ite
                (Term.mk_macro Term.q_exec_macro [] ts)
                (Term.mk_macro Term.q_out_macro [] ts)
                Term.mk_zero))
      in 
      Structured {
        name    = Symbols.q_frame;
        default = Term.empty;
        tinit   = Term.mk_zero;
        body    = (ts_v, body);
        rec_ty  = Type.ttimestamp;
        ty      = Type.tmessage;
      }
    in

    (*------------------------------------------------------------------*)
    let state =
      let body =
        Term.mk_proj 2 @@
        Term.mk_fun0
          Symbols.fs_qatt { fty = Symbols.ftype_builtin Symbols.fs_qatt; ty_args = [] }
          [ Term.mk_tuple
              [ ts;
                Term.mk_macro Term.q_frame_macro [] (Term.mk_pred ts);
                Term.mk_macro Term.q_state_macro [] (Term.mk_pred ts); ]]
      in 
      Structured {
        name    = Symbols.q_inp;
        default = qwitness;
        tinit   = qwitness;
        body    = (ts_v, body);
        rec_ty  = Type.ttimestamp;
        ty      = Type.tquantum_message;
      }
    in

    (*------------------------------------------------------------------*)
    let input =
      let body =
        Term.mk_proj 1 @@
        Term.mk_fun0
          Symbols.fs_qatt { fty = Symbols.ftype_builtin Symbols.fs_qatt; ty_args = [] }
          [ Term.mk_tuple
              [ ts;
                Term.mk_macro Term.q_frame_macro [] (Term.mk_pred ts);
                Term.mk_macro Term.q_state_macro [] (Term.mk_pred ts); ]]
      in 
      Structured {
        name    = Symbols.q_inp;
        default = Term.empty;
        tinit   = Term.empty;
        body    = (ts_v, body);
        rec_ty  = Type.ttimestamp;
        ty      = Type.tmessage;
      }
    in

    (*------------------------------------------------------------------*)
    let exec =
      let body =
        Term.mk_and
          (Term.mk_macro Term.q_exec_macro [] (Term.mk_pred ts))
          (Term.mk_macro Term.q_cond_macro [] ts)
      in 
      Structured {
        name    = Symbols.q_exec;
        default = Term.mk_false;
        tinit   = Term.mk_true;
        body    = (ts_v, body);
        rec_ty  = Type.ttimestamp;
        ty      = Type.tboolean;
      }
    in

    (*------------------------------------------------------------------*)
    let output = ProtocolMacro `Output in
    let cond   = ProtocolMacro `Cond   in 

  (*------------------------------------------------------------------*)
    {
      np          = Symbols.top_npath;
      rec_ty      = Type.ttimestamp;
      input_name  = Symbols.q_inp;
      output_name = Symbols.q_out;
      cond_name   = Symbols.q_cond;
      macros      = [Symbols.q_frame, frame ;
                     Symbols.q_inp  , input ;
                     Symbols.q_exec , exec  ;
                     Symbols.q_out  , output;
                     Symbols.q_state, state ;
                     Symbols.q_cond , cond  ; ];
    }
end (* PostQuantum *)

  (*------------------------------------------------------------------*)
let builtin_exec_models table = [Classical.model table; PostQuantum.model table]

let define_execution_models table : Symbols.table = 
  List.fold_left (fun table em ->
      List.fold_left (fun table (name,data) -> 
          let data = Symbols.Macro (General (Macro_data data)) in
          Symbols.Macro.redefine table ~data name
        ) table em.macros
    ) table (builtin_exec_models table)

(*------------------------------------------------------------------*)
(** {2 Global macro definitions} *)

(** Data associated with global macro symbols.
    The definition of these macros is not naturally stored as part
    of action descriptions, but directly in the symbols table. *)
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

  exec_model : exec_model; 
  (** The execution model this macro was declared in*)
  
  ty : Type.ty;
  (** The type of the macro, which does not depends on the system. *)
}

(*------------------------------------------------------------------*)
type Symbols.global_macro_def += Global_data of global_data

let data_of_global_data (d : global_data) : Symbols.data =
  Symbols.Macro (Global (List.length d.indices, d.ty, Global_data d))

(*------------------------------------------------------------------*)
let _pp ppe fmt (g : global_data) : unit =
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
       (Fmt.parens (Fmt.pair ~sep:Fmt.comma System.Single.pp (Term._pp ppe))))
    g.bodies

let pp     = _pp (default_ppe ~dbg:false ())
let pp_dbg = _pp (default_ppe ~dbg:true  ())

(*------------------------------------------------------------------*)
let get_global_data : Symbols.global_macro_def -> global_data = function
  | Global_data g -> g
  | _ -> assert false
    
let as_global_macro : Symbols.data -> global_data = function
  | Symbols.Macro Global (_, _, g) -> get_global_data g 
  | _ -> assert false

(*------------------------------------------------------------------*)
(** Get body of a global macro for a single system. *)
let get_single_body table (single : S.Single.t) (data : global_data) : Term.term =
  try List.assoc single data.bodies with
  | Not_found -> Library.Prelude.mk_witness table ~ty_arg:data.ty
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
    table system exec_model macro ~suffix ~action ~inputs ~indices ~ts body ty
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
    {action = (suffix, action); 
     inputs; indices; ts; bodies; ty; 
     exec_model; }
  in  
  let data = data_of_global_data glob_data in
  Symbols.Macro.declare ~approx:true table macro ~data 

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

(** Get the ftype of a macro. 
    The second argument is the type of the variable we are recursing
    upon (i.e. the variable after the `@` *)
let fty (table : Symbols.table) (ms : Symbols.macro) : Type.ftype * Type.ty =
  let fty_args, fty_out, rec_ty =
    match Symbols.get_macro_data ms table with
    | Symbols.Global (_, ty, data) ->
      let data = get_global_data data in
      List.map Vars.ty data.indices, ty, Type.ttimestamp
    | General def ->
      begin
        match get_general_macro_data def with
        | Structured     data   -> [],       data.ty, data.rec_ty
        | ProtocolMacro `Output -> [], Type.tmessage, Type.ttimestamp
        | ProtocolMacro `Cond   -> [], Type.tboolean, Type.ttimestamp
      end

    | Symbols.State (_,ty,data) ->
      begin
        match data with
        | StateInit_data (vs,_) -> List.map Vars.ty vs, ty, Type.ttimestamp
        | _ -> assert false
      end
  in
  (* FIXME: quantum: allow other types than [timestamp] *)
  assert (Type.equal rec_ty Type.ttimestamp);
  Type.mk_ftype [] fty_args fty_out, rec_ty

(*------------------------------------------------------------------*)
let is_global table (ms : Symbols.macro) : bool =
  match Symbols.get_macro_data ms table with
  | Symbols.Global (_, _, _) -> true
  | _ -> false

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
let can_expand (name : Symbols.macro) (a : Term.term) table =
  match Symbols.get_macro_data name table with
  | General _ -> 
    (* A structed macro [m@A] can be always be expanded if [A] is an action. *)
    (* FIXME: quantum: this could be relaxed, as only [output] and [cond] can 
       only be expanded on precise actions. Other structed macros can be 
       safely expanded for any action that happens (e.g. [frame]). *)
    is_action a

  | State _ -> is_action a
  (* FIXME: quantum: same, this expantion condition can likely be relaxed *)

  | Global (_, _, Global_data {action = (strict,a0) }) ->
    (* We can only expand a global macro when [a0] is a prefix of [a],
       because a global macro m(...)@A refer to inputs of A and
       its sequential predecessors. *)
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
(** Exported, see `.mli`. *)
let global_defined_from
    table (m : Symbols.macro) : [`Strict | `Large] * Action.shape
  =
  let data = as_global_macro (Symbols.Macro.get_data m table) in
  data.action
  
(*------------------------------------------------------------------*)
(** find an action shape defined in [system] that is a suffix of
    [prefix_shape] *)
let find_shape_suffix_of
    table (system : SE.fset)
    (strict : [`Large | `Strict]) 
    (prefix_shape : 'a Action.t)
  : Action.shape
  =
  let found = ref None in
  SE.fold_descrs (fun (descr : Action.descr) () ->
      let shape = Action.get_shape_v descr.action in
      if is_prefix strict prefix_shape shape then found := Some shape;
    ) table system ();
  oget !found                 (* must always succeed *)

(** Exported.
    find the smallest prefix of [action] that is a suffix of
    [suffix] *)
let smallest_prefix 
    (strict : [`Large | `Strict]) 
    (suffix : 'a Action.t) (action : 'b Action.t) : 'b Action.t 
  =
  match strict with
  | `Large  -> List.take (List.length suffix    ) action
  | `Strict -> List.take (List.length suffix + 1) action

(*------------------------------------------------------------------*)
(** Give the definition of the global macro [symb(args)@action].
    All prefixes of [action] must be valid actions of the system, except 
    if [allow_dummy] is true. *)
let get_def_glob
   ~(allow_dummy : bool)
    (system : SE.fset)
    (table  : Symbols.table)
    (_symb  : Term.msymb)
    ~(args  : Term.term list)
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

  let ts =                      (* a bit complex because of dummy actions *)
    let strict, prefix_shape = data.action in
    let ts_action =
      if allow_dummy then
        let shape = find_shape_suffix_of table system strict prefix_shape in
        Action.dummy shape
      else smallest_prefix strict prefix_shape action
    in
    SE.action_to_term table system ts_action
  in
    
  let ts_subst = Term.ESubst (Term.mk_var data.ts, ts) in
  (* Compute the relevant part of the action, i.e. the
     prefix of length [length inputs], reversed. *)
  let rev_action =
    let rec drop n l = if n=0 then l else drop (n-1) (List.tl l) in
    drop (List.length action - List.length data.inputs) (List.rev action)
  in

  let input_macro = 
    match data.exec_model with
    | Classical   -> Term.in_macro
    | PostQuantum -> Term.q_in_macro
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
         let in_tm = Term.mk_macro input_macro [] a_ts in
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
  let exception Failed in
  let failed () = raise Failed in

  let init_or_generic ~init ~body =
    let var, t = body in
    let subst = Term.ESubst (Term.mk_var var, Term.mk_action asymb aidx) in
    if asymb = Symbols.init_action then init else Term.subst [subst] t
  in

  let doit () =
    let action = Action.of_term asymb aidx table in
    
    (* we do not apply the substitution right away, as it may fail by
       trying to substitute indices by non-variable terms. *)
    let unapplied_descr, descr_subst =
      try SE.descr_of_action table system action with
      | Not_found -> failed ()
      (* fails if the action is not defined in the current system 
         (because it comes from another uncompatible system) *)
    in
    match Symbols.get_macro_data symb.s_symb table with
    | General data ->
      begin
        match get_general_macro_data data with
        (* TODO: quantum: allow arguments in generic structured macros *)
        | Structured data -> init_or_generic ~init:data.tinit ~body:data.body
        | ProtocolMacro `Output -> 
          Term.subst descr_subst (snd unapplied_descr.output)
        | ProtocolMacro `Cond ->
          Term.subst descr_subst (snd unapplied_descr.condition)
      end

    | State _ ->
      begin try
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
            Term.mk_ite
              (Term.mk_eqs ~simpl:true args ns_args)
              msg
              (Term.mk_macro symb args (Term.mk_pred (Term.mk_action asymb aidx)))
              
        with Not_found ->
          Term.mk_macro symb args (Term.mk_pred (Term.mk_action asymb aidx))
      end

    | Global (_,_,gdata) ->
      let {action = (strict, glob_a)} as gdata = get_global_data gdata in
      if is_prefix strict glob_a (Action.get_shape action)
      then
        get_def_glob 
          ~allow_dummy:false system table
          symb ~args  action gdata
      else failed ()
  in
  try `Def (doit ()) with Failed -> `Undef
    
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
  if not (SE.is_fset cntxt.system) then `MaybeDef else
    match SE.to_fset cntxt.system with
    | system ->
      (* Try to find an action equal to [ts] in [cntxt]. *)
      let ts_action =
        if can_expand symb.s_symb ts cntxt.table
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

  get_def_glob ~allow_dummy:true
    system table symb ~args dummy_action gdata

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
          data_of_global_data 
            { gdata with bodies = (new_system, body) :: gdata.bodies }
        in
        Symbols.Macro.redefine table ~data ms 
      end

