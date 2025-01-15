module L = Location

(*------------------------------------------------------------------*)
type p_param_val = Config.p_param_val
type Symbols.data += Config_data of p_param_val

let declare table (s:Symbols.lsymb) (v:p_param_val) = 
  let data = Config_data v in
  if Symbols.Config.mem_sp ([],L.unloc s) table then
    let ns = Symbols.Config.convert_path ([],s) table in
    Symbols.Config.redefine table ~data ns 
  else 
    fst (Symbols.Config.declare ~approx:false table s ~data )

(*------- Import from Config for default params --------------------*)

let s_timeout = "timeout"
let vint_timeout = 10
let v_timeout = Config.Param_int vint_timeout

let s_interactive = "interactive"
let v_interactive = Config.Param_bool false

let s_print_equ = "printTRSEquations"
let v_print_equ = Config.Param_bool false

let s_debug_constr = "debugConstr"
let v_debug_constr = Config.Param_bool false

let s_debug_completion = "debugCompletion"
let v_debug_completion = Config.Param_bool false

let s_debug_tactics = "debugTactics"
let v_debug_tactics = Config.Param_bool false

let s_verbose_crypto = "verboseCrypto"
let v_verbose_crypto = Config.Param_bool false

let s_strict_alias_mode = "processStrictAliasMode"
let v_strict_alias_mode = Config.Param_bool false

let s_show_strengthened_hyp = "showStrengthenedHyp"
let v_show_strengthened_hyp = Config.Param_bool false

let s_auto_fadup = "autoFADup"
let v_auto_fadup = Config.Param_bool true

let s_new_ind = "newInduction"
let v_new_ind = Config.Param_bool false

let s_post_quantum = "postQuantumSound"
let v_post_quantum = Config.Param_bool false

let s_prettyprint_reify = "prettyPrintReify"
let v_prettyprint_reify = Config.Param_bool true

let mk c = Location.mk_loc Location._dummy c

let decl (s:string) (v:p_param_val) (table:Symbols.table) : Symbols.table =
  declare table (mk s) v

let reset_params (table:Symbols.table) : Symbols.table =
  table
  |> decl s_timeout               v_timeout 
  |> decl s_interactive           v_interactive
  |> decl s_print_equ             v_print_equ
  |> decl s_debug_constr          v_debug_constr
  |> decl s_debug_completion      v_debug_completion
  |> decl s_debug_tactics         v_debug_tactics
  |> decl s_strict_alias_mode     v_strict_alias_mode
  |> decl s_show_strengthened_hyp v_show_strengthened_hyp
  |> decl s_auto_fadup            v_auto_fadup
  |> decl s_new_ind               v_new_ind
  |> decl s_post_quantum          v_post_quantum
  |> decl s_verbose_crypto        v_verbose_crypto
  |> decl s_prettyprint_reify     v_prettyprint_reify


let get_int s table : int = 
  let ns = Symbols.Config.convert_path ([], mk s) table in
  match Symbols.Config.get_data ns table with
  | Config_data (Config.Param_int i) -> i
  | _ -> assert false

let get_bool s table : bool = 
  let ns = Symbols.Config.convert_path ([],mk s) table in
  match Symbols.Config.get_data ns table with
  | Config_data (Config.Param_bool i) -> i
  | _ -> assert false

let solver_timeout = get_int s_timeout
let print_trs_equations = get_bool s_print_equ
let interactive = get_bool s_interactive
let debug_constr = get_bool s_debug_constr
let debug_completion = get_bool s_debug_completion
let debug_tactics = get_bool s_debug_tactics
let strict_alias_mode = get_bool s_strict_alias_mode
let show_strengthened_hyp = get_bool s_show_strengthened_hyp
let auto_fadup = get_bool s_auto_fadup
let new_ind = get_bool s_new_ind
let post_quantum = get_bool s_post_quantum
let verbose_crypto = get_bool s_verbose_crypto
let prettyprint_reify = get_bool s_prettyprint_reify

let set_param (s,p:string*p_param_val) table = 
  declare table (mk s) p
