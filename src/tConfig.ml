(*------------------------------------------------------------------*)
(* parser types *)

(*------------------------------------------------------------------*)
(* table with config namespace *)
include Symbols.Config
(* type config = ns Symbols.t *)
(* type t = config *)

type param_kind = Symbols.param_kind

type p_param_val = Config.p_param_val


type Symbols.data += Config_data of p_param_val

let def_of_param = function
  | Config.Param_bool _ -> Symbols.PBool
  | Config.Param_int _ -> Symbols.PInt
  | Config.Param_string _ -> Symbols.PString

let declare table (s:Theory.lsymb) (v:p_param_val) = 
  let data = Config_data v in
  if Symbols.Config.mem_lsymb s table then
    let ns = Symbols.Config.of_lsymb s table in
    Symbols.Config.redefine table ~data:data ns (def_of_param v)
  else 
    fst (Symbols.Config.declare table s ~data:data (def_of_param v))

(*------- Import from Config for default params --------------------*)

let s_timeout = "timeout"
let vint_timeout = 2
let v_timeout = Config.Param_int vint_timeout

let s_print_equ = "printTRSEquations"
let v_print_equ = Config.Param_bool false

let s_debug_constr = "debugConstr"
let v_debug_constr = Config.Param_bool false

let s_debug_completion = "debugCompletion"
let v_debug_completion = Config.Param_bool false

let s_debug_tactics = "debugTactics"
let v_debug_tactics = Config.Param_bool false

let s_strict_alias_mode = "processStrictAliasMode"
let v_strict_alias_mode = Config.Param_bool false

let s_show_strengthened_hyp = "showStrengthenedHyp"
let v_show_strengthened_hyp = Config.Param_bool false

let s_auto_intro = "autoIntro"
let v_auto_intro = Config.Param_bool false

let s_auto_fadup = "autoFADup"
let v_auto_fadup = Config.Param_bool true

let s_new_ind = "newInduction"
let v_new_ind = Config.Param_bool false

let s_old_completion = "oldCompletion"
let v_old_completion = Config.Param_bool false

let s_post_quantum = "postQuantumSound"
let v_post_quantum = Config.Param_bool false

let mk c = Location.mk_loc Location._dummy c

let decl (s:string) (_:param_kind) (v:p_param_val)
    (table:Symbols.table) : Symbols.table =
  declare table (mk s) v

let reset_params (table:Symbols.table) : Symbols.table =
      decl s_timeout Symbols.PInt v_timeout table
  |>  decl s_print_equ Symbols.PBool v_print_equ
  |>  decl s_debug_constr Symbols.PBool v_debug_constr
  |>  decl s_debug_completion Symbols.PBool v_debug_completion
  |>  decl s_debug_tactics Symbols.PBool v_debug_tactics
  |>  decl s_strict_alias_mode Symbols.PBool v_strict_alias_mode
  |>  decl s_show_strengthened_hyp Symbols.PBool v_show_strengthened_hyp
  |>  decl s_auto_intro Symbols.PBool v_auto_intro
  |>  decl s_auto_fadup Symbols.PBool v_auto_fadup
  |>  decl s_new_ind Symbols.PBool v_new_ind
  |>  decl s_old_completion Symbols.PBool v_old_completion
  |>  decl s_post_quantum Symbols.PBool v_post_quantum


let get_int s table : int = 
  let ns = Symbols.Config.of_lsymb (mk s) table in
  match Symbols.Config.get_data ns table with
  | Config_data (Config.Param_int i) -> i
  | _ -> assert false

let get_bool s table : bool = 
  let ns = Symbols.Config.of_lsymb (mk s) table in
  match Symbols.Config.get_data ns table with
  | Config_data (Config.Param_bool i) -> i
  | _ -> assert false

let [@warning "-32"] get_string s table : string = 
  let ns = Symbols.Config.of_lsymb (mk s) table in
  match Symbols.Config.get_data ns table with
  | Config_data (Config.Param_string s) -> s
  | _ -> assert false

    (*OK*)
let solver_timeout = get_int s_timeout
    (*OK*)
let print_trs_equations = get_bool s_print_equ
    (* a real global variable ? *)
let debug_constr = get_bool s_debug_constr
    (* a real global variable ? *)
let debug_completion = get_bool s_debug_completion
    (* a real global variable ? *)
let debug_tactics = get_bool s_debug_tactics
    (*OK*)
let strict_alias_mode = get_bool s_strict_alias_mode
    (*OK*)
let show_strengthened_hyp = get_bool s_show_strengthened_hyp
    (*OK*)
let auto_intro = get_bool s_auto_intro
    (*OK*)
let auto_fadup = get_bool s_auto_fadup
    (* FIXME never used ? *)
let new_ind = get_bool s_new_ind
    (* FIXME relevant ? *)
let old_completion = get_bool s_old_completion
    (*OK*)
let post_quantum = get_bool s_post_quantum

let set_param (s,p:string*p_param_val) table = 
  Format.eprintf "set %s…\n" s;
  declare table (mk s) p
