open Utils
open Ppenv

module L = Location
module S = System
module SE = SystemExpr
module Mv = Vars.Mv
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

(** See `.mli`. *)
type body = {
  vars      : Vars.vars;         (** The free variables of the pattern matching. *)
  pattern   : Term.term option;  (** The optional pattern *)
  when_cond : Term.term;         (** The condition *)
  out       : Term.term;         (** The output *)
}


let _pp_body ppe fmt (b : body) : unit =
  Fmt.pf fmt "@[<v>vars: @[%a@]@;\
              pattern: @[%a@]@;\
              when_cond: @[%a@]@;\
              out: @[%a@]@;\
              @]%!"    
    (Vars._pp_typed_list ppe) b.vars
    (Fmt.option (Term._pp ppe)) b.pattern
    (Term._pp ppe) b.when_cond
    (Term._pp ppe) b.out

let pp_body     = _pp_body (default_ppe ~dbg:false ())
let pp_body_dbg = _pp_body (default_ppe ~dbg:true  ())

(* note that there is a nicer pretty-printer in the
   [structed_macro_data] pretty-printer *)

(*------------------------------------------------------------------*)
(** See `.mli`. *)
type rw_strategy = Exhaustive | Exact |  Opaque

(*------------------------------------------------------------------*)
(** See `.mli`. *)
type in_systems =
  | Any 
  | Like of System.t 
  | Systems of SE.t 

(*------------------------------------------------------------------*)
(** See `.mli`. *)
type structured_macro_data = {
  name                : Symbols.macro;
  params              : Vars.vars;
  dist_param          : Vars.var option;
  bodies              : body list;
  ty                  : Type.ty;
  in_systems          : in_systems;
  rw_strat            : rw_strategy;
  info                : Term.macro_info;
  decreasing_quantity : Term.term option;
  decreasing_measure  : Symbols.fname;
}

(*------------------------------------------------------------------*)
let _pp_structured_macro_data ppe fmt s =
  let pp_in_systems fmt =
    match s.in_systems with
    | Any -> ()
    | Systems p -> Fmt.pf fmt " @system:(%a)" SE.pp p
    | Like    s -> Fmt.pf fmt " @like:%a" Symbols.pp_path s
  in
  let pp_body fmt b =
    let pp_pattern fmt =
      match b.pattern with
      | None -> Fmt.pf fmt "_"
      | Some pattern ->
        Fmt.pf fmt "%a" (Term._pp ppe) pattern
    in
    let pp_when fmt =
      if not (Term.equal b.when_cond Term.mk_true) then
        Fmt.pf fmt "when %a " (Term._pp ppe) b.when_cond
    in
    Fmt.pf fmt "@[<hov 2>@[| @[%t@] @[%t@]@]->@ %a@]"
      pp_pattern pp_when
      (Term._pp ppe) b.out
  in
  let pp_args fmt args =
    if args = [] then () 
    else
      Fmt.pf fmt "(%a) " (Vars._pp_typed_list ppe) args
  in
  let pp_bodies fmt =
    if s.info.is_match then
      Fmt.pf fmt "with@ @[<v 0>%a@]"
        (Fmt.list ~sep:(Fmt.any "@;") pp_body) s.bodies
    else 
      begin
        let single_body = as_seq1 s.bodies in
        assert (Term.equal single_body.when_cond Term.mk_true && 
                single_body.pattern = None &&
                single_body.vars = []);
        Fmt.pf fmt "=@ @[%a@]" (Term._pp ppe) single_body.out
      end
  in
  Fmt.pf fmt "@[<hv 2>@[let%s %a%t %a: %a @]%t@]"
    (if s.info.is_rec then " rec" else "")
    Symbols.pp_path s.name 
    pp_in_systems
    pp_args (s.params @ Option.to_list s.dist_param)
    Type.pp s.ty
    pp_bodies

(*------------------------------------------------------------------*)
let pp_structured_macro_data = 
  _pp_structured_macro_data (default_ppe ~dbg:false ())

let pp_structured_macro_data_dbg = 
  _pp_structured_macro_data (default_ppe ~dbg:true ())
 
(*------------------------------------------------------------------*)
(* Given a body, refreshes the free variables.  Can be safely called
   over the result of Macros.unfold, which must make sure that
   body.vars contains the remaining free variables after unfolding. *)
let refresh_body (body:body) =
  let vars, subst = Term.refresh_vars body.vars in
  let out = Term.subst subst body.out in
  let when_cond = Term.subst subst body.when_cond in
  let pattern =
    match body.pattern with
      None -> None
    | Some pat -> Some (Term.subst subst pat) in
  {vars; pattern; out; when_cond}


let mk_term_of_bodies table (bodies : body list) (match_param : Term.term)  =
  match bodies with
  | [] -> assert false
  | p::_ ->
    let out_type = Term.ty p.out in
    List.fold_left
      (fun acc body ->
         let when_cond =
           match body.pattern with
           | None ->  body.when_cond
           | Some pat -> Term.mk_and (Term.mk_eq match_param pat) body.when_cond
         in
         if body.vars = [] then
           Term.mk_ite when_cond body.out acc
         else           
           Term.mk_find body.vars when_cond body.out acc           
      )
      (Library.Prelude.mk_witness table ~ty_arg:out_type)
      bodies

(** A general macro definition. *)
type general_macro_data =
  | Structured of structured_macro_data
  | ProtocolMacro of [`Output | `Cond]
(* FIXME: quantum: move all macro definitions in this type *)

  (** ad hoc macro definitions using action descriptions *)

type Symbols.general_macro_def += Macro_data of general_macro_data

let get_general_macro_data : Symbols.general_macro_def -> general_macro_data = function
    | Macro_data g -> g
    | _ -> assert false

let as_general_macro : Symbols.data -> general_macro_data = function
  | Symbols.Macro (General g) -> get_general_macro_data g
  | _ -> assert false

(*------------------------------------------------------------------*)
let get_rw_strat
    (table : Symbols.table) (symb : Term.msymb) : rw_strategy
  =
  match Symbols.get_macro_data symb.s_symb table with
  | General data ->
    begin
      match get_general_macro_data data with
      | Structured data -> data.rw_strat
      | ProtocolMacro _ -> Exact
    end        
  | State _ -> Exact
  | Global (_,_,_) -> Exact

let get_macro_info
    (table : Symbols.table) (symb : Symbols.macro) : Term.macro_info
  =
  match Symbols.get_macro_data symb table with
  | General data ->
    begin
      match get_general_macro_data data with
      | Structured data -> data.info
      | ProtocolMacro _ -> Term.macro_info_builtin
    end        
  | State _ | Global _ -> Term.macro_info_builtin


let get_macro_deacreasing_info 
    (table : Symbols.table) (symb : Symbols.macro) (rec_arg : Term.term) : Term.term * Symbols.fname
  =
  let lt = Library.Prelude.fs_lt in
  match Symbols.get_macro_data symb table with
  | General data ->
    begin
      match get_general_macro_data data with
      | Structured data ->
        begin
          match data.decreasing_quantity with
          | None -> rec_arg, lt
          | Some t ->
            let dist_param = oget data.dist_param in
            let subst = [Term.ESubst (Term.mk_var dist_param, rec_arg)] in
            Term.subst subst t, data.decreasing_measure
        end
      | ProtocolMacro _ -> rec_arg, lt
    end        
  | State _ | Global _ -> rec_arg, lt


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
(** {3 Builtin execution models} 
    
    When manually adding an execution model, 
    the code in `Iter.ml` must be adapted accordingly. *)

(*------------------------------------------------------------------*)
(** For all cases except [init]. *)
let mk_timestamp_body table (ts : Term.t) (out : Term.t) : body =
  { vars      = [];
    pattern   = None;
    when_cond = Term.mk_and (Library.Prelude.mk_neq table ts Term.init) (Term.mk_happens ts);
    out       = out}

(** For [init]. *)
let mk_timestamp_body_init out : body =
  { vars      = [];
    pattern   = Some Term.init;
    when_cond = Term.mk_true; (* init always happens, no need to check it *)
    out       = out}

(** For not happens case. *)
let mk_timestamp_body_default ts default : body =
  { vars      = [];
    pattern   = None;
    when_cond = Term.mk_not (Term.mk_happens ts);
    out       = default}


module Classic = struct

  let out_ty   = Type.tmessage
  let cond_ty  = Type.tboolean
  let inp_ty   = Type.tmessage
  let frame_ty = Type.tmessage
  let exec_ty  = Type.tboolean

  let info = Term.macro_info_builtin

  let inp   : Term.msymb = Term.mk_symb Symbols.Classic.inp ~info inp_ty
  let out   : Term.msymb = Term.mk_symb Symbols.Classic.out ~info out_ty
  let frame : Term.msymb = Term.mk_symb Symbols.Classic.frame ~info frame_ty
  let cond  : Term.msymb = Term.mk_symb Symbols.Classic.cond ~info cond_ty
  let exec  : Term.msymb = Term.mk_symb Symbols.Classic.exec ~info exec_ty

  let model table =
    let ts_v = Vars.mk (Ident.create "τ") Type.ttimestamp in
    let ts   = Term.mk_var ts_v in

    (*------------------------------------------------------------------*)
    let frame_data =
      let body_main =
        mk_timestamp_body table ts @@
        Term.mk_pair
          (Term.mk_macro frame [] (Term.mk_pred ts))
          (Term.mk_pair
             (Term.mk_of_bool (Term.mk_macro exec [] ts))
             (Term.mk_ite
                (Term.mk_macro exec [] ts)
                (Term.mk_macro out [] ts)
                Term.mk_zero))
      and body_init = mk_timestamp_body_init Term.mk_zero
      and body_default = mk_timestamp_body_default ts Term.empty in
      Structured {
        name                = Symbols.Classic.frame;
        params              = [];
        dist_param          = Some ts_v;
        bodies              = [body_main; body_init; body_default];
        ty                  = frame_ty;
        rw_strat            = Exact;
        in_systems          = Any;
        info                = Term.macro_info_builtin;
        decreasing_quantity = None;
        decreasing_measure  = Library.Prelude.fs_lt;
      }
    in

    (*------------------------------------------------------------------*)
    let input_data =
      let body_main =
        mk_timestamp_body table ts @@
        Term.mk_fun0
          Symbols.fs_att { fty = Symbols.ftype_builtin Symbols.fs_att; ty_args = [] }
          [Term.mk_macro frame [] (Term.mk_pred ts)]
      and body_init = mk_timestamp_body_init Term.empty
      and body_default = mk_timestamp_body_default ts Term.empty in
      Structured {
        name                = Symbols.Classic.inp;
        params              = [];
        dist_param          = Some ts_v;
        bodies              = [body_main; body_init; body_default];
        ty                  = inp_ty;
        rw_strat            = Exact;
        in_systems          = Any;
        info                = Term.macro_info_builtin;
        decreasing_quantity = None;
        decreasing_measure  = Library.Prelude.fs_lt;
      }
    in

    (*------------------------------------------------------------------*)
    let exec_data =
      let body_main =
        mk_timestamp_body table ts @@
        Term.mk_and
          (Term.mk_macro exec [] (Term.mk_pred ts))
          (Term.mk_macro cond [] ts)
      and body_init = mk_timestamp_body_init Term.mk_true
      and body_default = mk_timestamp_body_default ts Term.mk_false in
      Structured {
        name                = Symbols.Classic.exec;
        params              = [];
        dist_param          = Some ts_v;
        bodies              = [body_main; body_init; body_default];
        ty                  = exec_ty;
        rw_strat            = Exact;
        in_systems          = Any;
        info                = Term.macro_info_builtin;
        decreasing_quantity = None;
        decreasing_measure  = Library.Prelude.fs_lt;
      }
    in

    (*------------------------------------------------------------------*)
    let output_data = ProtocolMacro `Output in
    let cond_data   = ProtocolMacro `Cond in

    (*------------------------------------------------------------------*)
    {
      np          = Symbols.top_npath;
      rec_ty      = Type.ttimestamp;
      input_name  = Symbols.Classic.inp;
      output_name = Symbols.Classic.out;
      cond_name   = Symbols.Classic.cond;
      macros      = [Symbols.Classic.frame, frame_data ;
                     Symbols.Classic.inp  , input_data ;
                     Symbols.Classic.exec , exec_data  ;
                     Symbols.Classic.out  , output_data;
                     Symbols.Classic.cond , cond_data  ; ];
    } 
end (* Classic *)

(*------------------------------------------------------------------*)
module Quantum = struct

  let out_ty        = Type.tmessage
  let cond_ty       = Type.tboolean
  let inp_ty        = Type.tmessage
  let transcript_ty = Type.tmessage
  let state_ty      = Type.tquantum_message
  let frame_ty      = Type.tuple [Type.ttimestamp; Type.tquantum_message; Type.tmessage]
  let exec_ty       = Type.tboolean

  let info = Term.macro_info_builtin
  
  let out        : Term.msymb = Term.mk_symb Symbols.Quantum.out        ~info out_ty
  let cond       : Term.msymb = Term.mk_symb Symbols.Quantum.cond       ~info cond_ty
  let inp        : Term.msymb = Term.mk_symb Symbols.Quantum.inp        ~info inp_ty
  let transcript : Term.msymb = Term.mk_symb Symbols.Quantum.transcript ~info transcript_ty
  let state      : Term.msymb = Term.mk_symb Symbols.Quantum.state      ~info state_ty
  let frame      : Term.msymb = Term.mk_symb Symbols.Quantum.frame      ~info frame_ty
  let exec       : Term.msymb = Term.mk_symb Symbols.Quantum.exec       ~info exec_ty 

  let model table =
    let ts_v = Vars.mk (Ident.create "τ") Type.ttimestamp in
    let ts   = Term.mk_var ts_v in

    let qwitness = Library.Prelude.mk_witness table ~ty_arg:(Type.tquantum_message) in

    (*------------------------------------------------------------------*)
    let frame_data =
      let body_main =
        mk_timestamp_body table ts @@
        Term.mk_tuple
          [ts;
           Term.mk_macro state      [] ts;
           Term.mk_macro transcript [] ts; ]
      and body_init = mk_timestamp_body_init @@ Term.mk_tuple [Term.init; qwitness; Term.empty]
      and body_default = mk_timestamp_body_default ts @@ Term.mk_tuple [Term.init; qwitness; Term.empty  ] in
      Structured {
        name                = Symbols.Quantum.frame;
        params              = [];
        dist_param          = Some ts_v;
        bodies              = [body_main; body_init; body_default];
        ty                  = frame_ty;
        rw_strat            = Exact;
        in_systems          = Any;
        info                = Term.macro_info_builtin;
        decreasing_quantity = None;
        decreasing_measure  = Library.Prelude.fs_lt;
      }
    in

    (*------------------------------------------------------------------*)
    let transcript_data =
      let body_main =
        mk_timestamp_body table ts @@        
        Term.mk_pair 
          (Term.mk_macro transcript [] (Term.mk_pred ts))
          (Term.mk_pair
             (Term.mk_macro inp [] ts)
             (Term.mk_pair
                (Term.mk_of_bool (Term.mk_macro exec [] ts))
                (Term.mk_ite (Term.mk_macro exec [] ts) (Term.mk_macro out [] ts) Term.mk_zero)
             )
          )
      and body_init = mk_timestamp_body_init Term.empty
      and body_default = mk_timestamp_body_default ts Term.empty
      in
      Structured {
        name                = Symbols.Quantum.transcript;
        params              = [];
        dist_param          = Some ts_v;
        bodies              = [body_main; body_init; body_default];
        ty                  = transcript_ty;
        rw_strat            = Exact;
        in_systems          = Any;
        info                = Term.macro_info_builtin;
        decreasing_quantity = None;
        decreasing_measure  = Library.Prelude.fs_lt;
        }

    in
    (*------------------------------------------------------------------*)
    let state_data =
      let body_main =
        mk_timestamp_body table ts @@
        Term.mk_proj 2 @@
        Term.mk_fun0
          Symbols.fs_qatt { fty = Symbols.ftype_builtin Symbols.fs_qatt; ty_args = [] }
          [ Term.mk_macro frame [] (Term.mk_pred ts) ]
      and body_init = mk_timestamp_body_init qwitness
      and body_default = mk_timestamp_body_default ts qwitness in      
      Structured {
        name                =  Symbols.Quantum.state;
        params              = [];
        dist_param          = Some ts_v;
        bodies              = [body_main; body_init; body_default];
        ty                  = state_ty;
        rw_strat            = Exact;
        in_systems          = Any;
        info                = Term.macro_info_builtin;
        decreasing_quantity = None;
        decreasing_measure  = Library.Prelude.fs_lt;
      }
    in

    (*------------------------------------------------------------------*)
    let input_data =
      let body_main =
        mk_timestamp_body table ts @@
        Term.mk_proj 1 @@
        Term.mk_fun0
          Symbols.fs_qatt { fty = Symbols.ftype_builtin Symbols.fs_qatt; ty_args = [] }
          [ Term.mk_macro frame [] (Term.mk_pred ts) ]
      and body_init = mk_timestamp_body_init Term.empty
      and body_default = mk_timestamp_body_default ts Term.empty in
      Structured {
        name                =  Symbols.Quantum.inp;
        params              = [];
        dist_param          = Some ts_v;
        bodies              = [body_main; body_init; body_default];
        ty                  = inp_ty;
        rw_strat            = Exact;
        in_systems          = Any;
        info                = Term.macro_info_builtin;
        decreasing_quantity = None;
        decreasing_measure  = Library.Prelude.fs_lt;
      }
    in
    (*------------------------------------------------------------------*)
    let exec_data =
      let body_main =
        mk_timestamp_body table ts @@
        Term.mk_and
          (Term.mk_macro exec [] (Term.mk_pred ts))
          (Term.mk_macro cond [] ts)
      and body_init = mk_timestamp_body_init Term.mk_true
      and body_default = mk_timestamp_body_default ts Term.mk_false in
      Structured {
        name                = Symbols.Quantum.exec;
        params              = [];
        dist_param          = Some ts_v;
        bodies              = [body_main; body_init; body_default];
        ty                  = exec_ty;
        rw_strat            = Exact;
        in_systems          = Any;
        info                = Term.macro_info_builtin;
        decreasing_quantity = None;
        decreasing_measure  = Library.Prelude.fs_lt;
      }
    in
    (*------------------------------------------------------------------*)
    let output_data = ProtocolMacro `Output in
    let cond_data   = ProtocolMacro `Cond in 

  (*------------------------------------------------------------------*)
    {
      np          = Symbols.top_npath;
      rec_ty      = Type.ttimestamp;
      input_name  = Symbols.Quantum.inp;
      output_name = Symbols.Quantum.out;
      cond_name   = Symbols.Quantum.cond;
      macros      = [Symbols.Quantum.frame     , frame_data      ;
                     Symbols.Quantum.transcript, transcript_data ;
                     Symbols.Quantum.inp       , input_data      ;
                     Symbols.Quantum.exec      , exec_data       ;
                     Symbols.Quantum.out       , output_data     ;
                     Symbols.Quantum.state     , state_data      ;
                     Symbols.Quantum.cond      , cond_data       ; ];
    }
end (* PostQuantum *)

  (*------------------------------------------------------------------*)
let builtin_exec_models table = [Classic.model table; Quantum.model table]

let define_execution_models table : Symbols.table =
  List.fold_left (fun table em ->
      List.fold_left (fun table (name,data) ->
          let data = Symbols.Macro (General (Macro_data data)) in
          Symbols.Macro.redefine table ~data name
        ) table em.macros
    ) table (builtin_exec_models table)

(*------------------------------------------------------------------*)
(** {2 Global macro definitions} *)

(** Data as.sociated with global macro symbols.
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

  exec_model : Action.exec_model; 
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

type rec_arg_ty = [`At of Type.ty | `Standard of Type.ty | `None]

(** see `.mli` *)
let fty
    (table : Symbols.table) 
    (ms : Symbols.macro) 
  : Type.ftype * rec_arg_ty
  =
  let fty_args, fty_out, rec_ty =
    match Symbols.get_macro_data ms table with
    | Symbols.Global (_, ty, data) ->
      let data = get_global_data data in
      List.map Vars.ty data.indices, ty, `At Type.ttimestamp
    | General def ->
      begin
        match get_general_macro_data def with
        | Structured     data   ->
          let rec_ty =
            match data.dist_param with
            | None -> `None
            | Some v -> 
              match data.info.pp_style with
              | `At        -> `At (Vars.ty v) 
              | `Standard -> `Standard (Vars.ty v)
          in
          List.map Vars.ty data.params, data.ty, rec_ty
        | ProtocolMacro `Output -> [], Type.tmessage, `At Type.ttimestamp
        | ProtocolMacro `Cond   -> [], Type.tboolean, `At Type.ttimestamp
      end

    | Symbols.State (_,ty,data) ->
      begin
        match data with
        | StateInit_data (vs,_) -> List.map Vars.ty vs, ty, `At Type.ttimestamp
        | _ -> assert false
      end
  in
  Type.mk_ftype [] fty_args fty_out, rec_ty

(*------------------------------------------------------------------*)
let msymb (table : Symbols.table) (symb : Symbols.macro) : Term.msymb =
  let fty, _ = fty table symb in
  let info = get_macro_info table symb in
  Term.mk_symb symb ~info fty.fty_out

(*------------------------------------------------------------------*)
let is_global table (ms : Symbols.macro) : bool =
  match Symbols.get_macro_data ms table with
  | Symbols.Global (_, _, _) -> true
  | _ -> false

(*------------------------------------------------------------------*)
(** {2 Macro expansions} *)

let is_prefix strict a b =
  match Action.distance a b with
  | None -> false     (* [a] not prefix of [b] *)
  | Some i -> match strict with
    | `Large -> true
    | `Strict -> i > 0

(*------------------------------------------------------------------*)
(** Give the **internal** definition of a global macro.
    Meaningless when working in a sequent.
    Used for global rewriting, when rewriting in another global macro. *)
let get_def_glob_internal
    (table : Symbols.table) (system : SE.fset)
    (symb : Term.msymb)  ~(args : Term.term list)
    ~(ts : Term.term) (inputs : Vars.vars option)
  : Term.term * Vars.vars
  =
  assert (is_global table symb.s_symb);

  let data = as_global_macro (Symbols.Macro.get_data symb.s_symb table) in
  let body = get_body table system data in

  let subst =
    (match inputs with
     | None -> []
     | Some inputs ->
       let prefix_inputs = List.take (List.length data.inputs) inputs in       
       List.map2
         (fun i i' -> Term.ESubst (Term.mk_var i, Term.mk_var i'))
         data.inputs prefix_inputs
    )
    @
    List.map2
      (fun i t' -> Term.ESubst (Term.mk_var i, t'))
      data.indices args
  in
  let subst = Term.ESubst (Term.mk_var data.ts, ts) :: subst in
  (Term.subst subst body, data.inputs)

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
    | Classic     -> Classic.inp
    | PostQuantum -> Quantum.inp
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
(** Match a pattern [pattern] with [t]. 
    [pattern] must be a pattern-matching pattern (see
    [ProcessDecl.check_pattern]): notably, no variable may occur more
    than once in [pattern]. *)
let basic_match
    (table : Symbols.table) 
    ~(term : Term.term) ~(pattern : Term.term)
  : [`Match of Term.subst | `MatchFailure | `Unknown]
  =
  let exception Failure in
  let exception Unknown in
  
  let mv : (Vars.var, Term.term) Hashtbl.t = Hashtbl.create 32 in

  let add_or_fail (v : Vars.var) t =
    (* each variable may only appear once in a pattern (see
       [ProcessDecl.check_pattern]) *)
    assert (not (Hashtbl.mem mv v));
    Hashtbl.add mv v t 
  in
  
  let rec aux (t1 : Term.term) (t2 : Term.term) : unit =
    match t1, t2 with
    | Term.Int i1, Term.Int i2 -> if not (Z.equal i1 i2) then raise Failure

    (* Int.( x1 + i1, i2) where [i2 >= i1] and [i1,i2] are concrete
       values *)
    | Term.App (Fun (fs1,_), [Var x1     ; Int i1]), Int i2
      when fs1 = Library.Int.add table && Z.leq i1 i2 ->
      add_or_fail x1 (Term.mk_int Z.(i2 - i1))

    (* Int.( x1 + i1, x2 + i2) where [i1 <= i2] and [i1,i2] are concrete
       values *)
    | Term.App (Fun (fs1,_), [Var x1     ; Int i1]),
      Term.App (Fun (fs2,_), [Var _ as x2; Int i2])
      when fs1 = Library.Int.add table &&
           fs2 = Library.Int.add table &&
           Z.leq i1 i2 ->
      add_or_fail x1 (Library.Int.mk_add table x2 (Term.mk_int Z.(i2 - i1)))

    | Term.Action (asymb1, aidx1), Term.Action (asymb2, aidx2) ->
      if asymb1 <> asymb2 then
        raise Failure;

      List.iter2 aux aidx1 aidx2

    | Term.App (t1,tl1), Term.App (t2,tl2) -> aux t1 t2; List.iter2 aux tl1 tl2

    | Term.Var x, _ -> add_or_fail x t2

    | _ -> raise Unknown
  in
  try
    aux pattern term;
    `Match
      (List.map (fun (v, t) ->
           Term.ESubst (Term.mk_var v, t))
          (Hashtbl.to_list mv))
  with
  | Failure -> `MatchFailure
  | Unknown -> `Unknown

(** not exported *)
exception UnfoldFailed
let unfold_failed () = raise UnfoldFailed

let unfold_structured_macro
    (env     : Env.t)
    (data    : structured_macro_data)
    (args    : Term.term list)
    (rec_arg : Term.term)
  : body list
  =
  let system = env.system.set in
  let table = env.table in

  (* Compute the projection substitution, if necessary *)
  let do_proj_subst =
    match data.in_systems with
    | Any -> fun x -> x
    | Like s ->
      begin
        match SE.get_compatible_system env.se_vars system with
        | None -> unfold_failed ()
        | Some p0 -> 
          if not (SystemSyntax.compatible table p0 s) then unfold_failed ()
      end;
      fun x -> x

    | Systems p ->
      if SE.is_var system then unfold_failed ();
      let system = SE.to_arbitrary system in
      (* FIXME: replace with subset_modulo + projection, as already
         done in [sequent.ml] *)
      if not (SE.subset_modulo table system p) then unfold_failed ();

      (* The macro was defined using the projections in [p], but we
         want to unfold the macro in [system]. 
         C.f. description of the [in_systems] data-type. 
         (Note [p]'s projections are all distincts.) *)
      let _, proj_subst =
        SE.mk_proj_subst ~strict:false ~src:p ~dst:system
      in
      Term.subst_projs ~project:true proj_subst 
  in

  let subst =
    (omap_dflt []
       (fun dist_param -> [Term.ESubst (Term.mk_var dist_param, rec_arg)]) 
       data.dist_param
    )
    @
    (List.map2
       (fun i t -> Term.ESubst (Term.mk_var i, t))
       data.params
       args
    )
  in

  (* apply the projection substitution and the substitution [subst]
     to [body] *)
  let do_subst subst body =
    let doit = do_proj_subst -| Term.subst subst in
    { body with
      when_cond = doit body.when_cond;
      out       = doit body.out;
    }
  in

  (* compute the bodies *)
  List.fold_left (fun acc body ->
      (* avoid capture between [subst]'s domain and [body.vars] *)
      let body = refresh_body body in
      match body.pattern with
      | None -> do_subst subst body :: acc
      | Some pat ->
        match basic_match table ~pattern:pat ~term:rec_arg with
        | `Match rec_subst -> 
          (* the match succeeded, so we clear the match and
             pattern variables *)
          let body = { body with vars = []; pattern = None; } in
          do_subst (rec_subst @ subst) body
          :: acc
        | `Unknown         -> do_subst (subst) body :: acc
        | `MatchFailure -> acc
    ) [] data.bodies

(*------------------------------------------------------------------*)
type expand_context = InSequent | InGlobal of { inputs : Vars.vars }


let not_happens_macro_body ty ts =
  { vars=[];
    pattern=None;
    when_cond=(
      let hap = (Term.mk_happens ts) in
      Term.mk_not hap);
    out = if ty = Type.tboolean then Term.mk_false else Term.empty;
    (* In general, we would need a default value for every possible type. *)
  }

let init_macro_body ty =
  { vars=[];
    pattern=Some Term.init;
    when_cond=Term.mk_true;
    out = if ty = Type.tboolean then Term.mk_true else Term.empty;
    (* In general, we would need a default value for every possible type. *)
    }

(*------------------------------------------------------------------*)
let _unfold
    ?(expand_context = InSequent)
    (env     : Env.t)
    (symb    : Term.msymb)
    (args    : Term.term list)
    (rec_arg : Term.term)
  : body list
  =
  let exception MatchFailed in
  let match_failed () = raise MatchFailed in
  let table = env.table in
  let system = env.system.set in

  (* fails if the action is not defined in the current system
     (because it comes from another uncompatible system) *)
  match Symbols.get_macro_data symb.s_symb table with
  | General data ->
    begin
      match get_general_macro_data data with
      | Structured data ->
        unfold_structured_macro env data args rec_arg

      | ProtocolMacro `Output ->
        if not (SE.is_fset system) then unfold_failed ();
        let fset_system = SE.to_fset system in

        begin
          try
            let unapplied_descr, descr_subst =
              match rec_arg with
              |Term.Action(asymb, aidx) ->
                let action = Action.of_term asymb aidx table in
                (try SE.descr_of_action table fset_system action with
                 | Not_found ->
                   (* output{se}@A when A not in SE is a typing error. *)
                   assert false)
              | _ -> match_failed ()
            in
            [{
              vars =[];
              pattern = None;
              when_cond =
                if Term.equal rec_arg Term.init then
                  Term.mk_true
                else Term.mk_happens rec_arg;
              out = Term.subst descr_subst (snd unapplied_descr.output)
            }]
          with
          | MatchFailed->
            (* output@tau when not(happens(tau)) *)
            (not_happens_macro_body Type.tmessage rec_arg)
            ::
            (* output@init *)
            (init_macro_body Type.tmessage)
            (* output@A for all actions A *)
            ::                           
            SE.fold_descrs
              (fun (descr : Action.descr) (bodies : body list) ->
                 let action =
                   SE.action_to_term table fset_system @@
                   Action.to_action descr.action
                 in
                 (* init is covered by fold_descrs, but
                    we handle it more cleanly before *)
                 if Term.equal action Term.init then
                   bodies
                 else
                   {vars=Action.get_args_v descr.action;
                    pattern= Some action;
                    when_cond =
                      if Term.equal action Term.init then
                        Term.mk_true
                      else Term.mk_happens action;
                    out = snd descr.output} :: bodies
              ) table fset_system []
        end

      | ProtocolMacro `Cond ->
        if not (SE.is_fset system) then unfold_failed ();
        let fset_system = SE.to_fset system in

        begin
          try
            let unapplied_descr, descr_subst =
              match rec_arg with
              |Term.Action(asymb, aidx) ->
                let action = Action.of_term asymb aidx table in
                (try SE.descr_of_action table fset_system action with
                 | Not_found -> 
                   (* cond{se}@A when A not in SE is a typing error. *)
                   assert false)
              | _ -> match_failed ()
            in
            [{
              vars =[];
              pattern = None;
              when_cond =
                if Term.equal rec_arg Term.init then
                  Term.mk_true
                else Term.mk_happens rec_arg;
              out = Term.subst descr_subst (snd unapplied_descr.condition)
            }]

          with
          | MatchFailed->
            (* cond@tau when not(happens(tau)) *)
            (not_happens_macro_body Type.tboolean rec_arg)
            ::
            (* cond@init  *)
            (init_macro_body Type.tboolean)
            (* cond@A for all actions A *)
            ::                           
            SE.fold_descrs
              (fun (descr : Action.descr) (bodies : body list) ->
                 let action = SE.action_to_term table fset_system
                   @@ Action.to_action descr.action
                 in
                 (* init is covered by fold_descrs, but
                    we handle it more cleanly before *)
                 if Term.equal action Term.init then
                   bodies
                 else                              
                   {vars=Action.get_args_v descr.action;
                    pattern= Some action;
                    when_cond =
                      if Term.equal action Term.init then
                        Term.mk_true
                      else Term.mk_happens action;
                    out = snd descr.condition} :: bodies                      
              ) table fset_system []
        end
    end

  | State _ ->
    if not (SE.is_fset system) then unfold_failed ();
    let fset_system = SE.to_fset system in

    begin
      try    
        let unapplied_descr, descr_subst =
          match rec_arg with
          |Term.Action(asymb, aidx) ->
            let action = Action.of_term asymb aidx table in
            (try
               SE.descr_of_action table fset_system action
             with Not_found ->
               (* state{se}@A with A not in se *)
               assert false)
          | _ -> match_failed ()
        in

        (* Look for an update of the state macro [name] in the updates
           of [action]; we rely on the fact that [action] can only contain
           a single update for each state macro symbol *)
        let (ns_params, msg) : Term.terms * Term.term =
          let _, ns_params, msg =
            List.find (fun (ns,ns_params,_) ->
                ns = symb.s_symb &&
                List.length ns_params = List.length args
              ) unapplied_descr.updates
          in
          List.map (Term.subst descr_subst) ns_params, Term.subst descr_subst msg
        in

        (* Init case: we substitute the indices by their definition. *)
        if Term.equal rec_arg Term.init then
          let s = List.map2 (fun i1 i2 ->
              match i1 with
              | Term.Var _ -> Term.ESubst (i1, i2)
              | _ -> assert false
              (* impossible for well-formed action description for init *)
            ) ns_params args
          in
          [{ vars = [];
             pattern = None;
             when_cond = Term.mk_true;
             out = Term.subst s msg}]

        (* If indices [params] of the macro we want to expand
           are equal to indices [ns_params] corresponding to this macro
           in the action description, then the macro is expanded as defined
           by the update term. *)
        else if List.for_all2 Term.equal args ns_params then
          [{ vars = [];
             pattern = None;
             when_cond = Term.mk_happens rec_arg;
             out = msg}]
          (* Otherwise, we need to take into account the possibility that
             [param] and [ns_params] might be equal, and generate a conditional.  *)
        else
          [{ vars = [];
             pattern = None;
             when_cond = Term.mk_happens rec_arg;
             out = 
               Term.mk_ite
                 (Term.mk_eqs ~simpl:true args ns_params)
                 msg
                 (Term.mk_macro symb args (Term.mk_pred rec_arg))
           }]                  

      with
      | Not_found ->
        (* state{se}@A with state not updated by A *)
        [{ vars = [];
           pattern = None;
           when_cond =
             if Term.equal rec_arg Term.init then
               Term.mk_true
             else Term.mk_happens rec_arg;         
           out = Term.mk_macro symb args (Term.mk_pred rec_arg)
         }]

      | MatchFailed ->
        (* we are unfolding symb(args)@tau *)
        let st_bodies =
          SE.fold_descrs
            (fun (descr : Action.descr) (acc : body list) ->
               List.fold_left (fun acc (msymb, margs, body) ->
                   (* Represent the update [msymb(margs)@descr.action := body]. *)
                   if msymb = symb.s_symb then
                     let action = SE.action_to_term table fset_system
                       @@ Action.to_action descr.action
                     in                        
                     if Term.equal action Term.init then
                       (* we instantiate the arguments *)                                          
                       let subst =
                         List.map2 (fun i1 i2 ->
                             (* [i1] must be a variable for
                                well-formed init action *)
                             assert (Term.is_var i1);
                             Term.ESubst (i1, i2)
                         ) margs args
                       in
                       {vars= [];
                        pattern= Some Term.init ;
                        when_cond = Term.mk_true;
                        out = Term.subst subst body} :: acc
                     else
                       (* we build two possible results *)
                       let subst =
                         List.map2 (fun marg arg ->
                             Term.ESubst (marg, arg)
                           ) margs args
                       in                   
                       (* msymb(margs)@A[descr.action.args_v] *)
                       (* we are looking for possible unfolding of symb(args)@tau *)
                       (* The possibility is:
                          symb(args)@A[descr.action.args_v] :=
                             if margs=args then
                                body
                             else
                               symb(args)@pred(A[...])

                          This is in fact for instance S i @ A i' := 
                             if i=i' then
                                body
                             else
                                S i @pred(A i')
                       *)
                       (* we instantiate this with two different
                          bodies to improve path conditions, by in
                          fact saying that we have two possible
                          unrolings,, which are for `S i @ A i` and
                          `S i @ A i'` with `i<>i'`.
                       *)                                                       
                       {vars= Action.get_args_v descr.action;
                        pattern= Some action ;
                        when_cond = Term.mk_and
                            (Term.mk_happens action)
                            (Term.mk_not ((Term.mk_eqs ~simpl:true args margs)))
                       ;
                        out = (Term.mk_macro symb args (Term.mk_pred rec_arg))}

                       ::                              
                       {vars= Action.get_args_v descr.action;
                        pattern= Some (Term.subst subst action) ;
                        when_cond = Term.mk_happens @@ Term.subst subst action;
                        out = Term.subst subst body}
                       :: acc
                   else
                     acc
                 )
                 acc descr.updates                 
            )
            table fset_system []
        in
        st_bodies
    end

  | Global (_,_,gdat) ->
    if not (SE.is_fset system) then unfold_failed ();
    let fset_system = SE.to_fset system in
    
    try
      begin
        match expand_context with
        | InSequent ->
          begin
            let action =
              match rec_arg with
              |Term.Action(asymb, aidx) -> Action.of_term asymb aidx table
              | _ -> match_failed ()
            in
            let {action = (strict, glob_a)} as gdata = get_global_data gdat in

            (* We are unfolding [m@B] for a global macro [m] that we
               know is not defined at [B]. We decided to refuse to
               unfold the macro. Alternatively, we could decide to
               return a default value (e.g. [witness]). *)
            if not (is_prefix strict glob_a (Action.get_shape action)) then
              unfold_failed ();
            
            [{
              vars = [];
              pattern = None;
              when_cond = Term.mk_true;
              out = get_def_glob ~allow_dummy:false fset_system table
                  symb ~args action gdata}]
          end

        | InGlobal ins ->
          let t, _ =
            get_def_glob_internal
              table fset_system
              symb ~args ~ts:rec_arg (Some ins.inputs)
          in
          [{ vars = [];
             pattern = None;
             when_cond = Term.mk_true;
             out = t}]
      end

    with MatchFailed ->
      let {action = (strict, glob_a)} as gdata = get_global_data gdat in      
      let glob_bodies =
        SE.fold_descrs
          (fun (descr : Action.descr) (acc : body list) ->
             if is_prefix strict glob_a (Action.get_shape_v descr.action)
             then
               let action = Action.to_action descr.action in
               {vars=Action.get_args_v descr.action;
                pattern= Some (SE.action_to_term table fset_system @@ action);
                when_cond =
                  if Term.equal rec_arg Term.init then
                    Term.mk_true
                  else Term.mk_happens rec_arg;                                 
                out = get_def_glob ~allow_dummy:false fset_system table
                    symb ~args action gdata}
               :: acc
             else
               acc
          )
          table fset_system []
      in
      glob_bodies

let unfold
    ?(expand_context = InSequent)
    (env     : Env.t)
    (symb    : Term.msymb)
    (args    : Term.term list)
    (rec_arg : Term.term) :
  [ `Results of body list | `Unknown ]
  =
  match _unfold ~expand_context env symb args rec_arg with
  | exception UnfoldFailed -> `Unknown
  | bodies -> `Results (List.rev bodies)

(*------------------------------------------------------------------*)
(** Exported *)
let get_dummy_definition
    (table  : Symbols.table)
    (system : SE.fset)
    (symb   : Term.msymb)
    ~(args  : Term.term list)
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
