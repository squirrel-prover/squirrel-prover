module L = Location

(*------------------------------------------------------------------*)
type p_param_val =
  | Param_bool   of bool
  | Param_string of string
  | Param_int    of int

type p_set_param = Symbols.lsymb * p_param_val

(*------------------------------------------------------------------*)
type Symbols.data += Config_data of p_param_val

let as_data = function
  | Config_data d -> d
  | _ -> assert false

(*------------------------------------------------------------------*)
let get_kind = function
  | Param_bool   _ -> `Bool
  | Param_string _ -> `String
  | Param_int    _ -> `Int
    
let pp_kind fmt = function
  | `Bool   -> Fmt.pf fmt "bool"
  | `String -> Fmt.pf fmt "string"
  | `Int    -> Fmt.pf fmt "int"

(*------------------------------------------------------------------*)
(** declare a new configuration parameter *)
let declare (s:string) (v:p_param_val) table = 
  let data = Config_data v in
  assert (not (Symbols.Config.mem_sp ([],s) table));
  let s = L.mk_loc L._dummy s in
  fst (Symbols.Config.declare ~approx:false table s ~data )

(** set the value of an existing configuration parameter  *)
let set (s:Symbols.lsymb) (v:p_param_val) table =
  let ns = Symbols.Config.convert_path ([],s) table in
  let old_val = as_data (Symbols.Config.get_data ns table) in
  if get_kind old_val <> get_kind v then
    raise
      (Symbols.Error
         (L.loc s,
          Symbols.Failure (
            Fmt.str "bad parameter kind: %s expects a %a"
              (L.unloc s) pp_kind (get_kind old_val))
         )
      );
  
  let data = Config_data v in
  Symbols.Config.redefine table ~data ns 

(*------- Import from Config for default params --------------------*)

let s_timeout = "timeout"
let vint_timeout = 10
let v_timeout = Param_int vint_timeout

let s_interactive = "interactive"
let v_interactive = Param_bool false

let s_print_equ = "printTRSEquations"
let v_print_equ = Param_bool false

let s_debug_constr = "debugConstr"
let v_debug_constr = Param_bool false

let s_debug_completion = "debugCompletion"
let v_debug_completion = Param_bool false

let s_debug_tactics = "debugTactics"
let v_debug_tactics = Param_bool false

let s_verbose_crypto = "verboseCrypto"
let v_verbose_crypto = Param_bool false

let s_log_unsat_crypto = "logUnsatCrypto"
let v_log_unsat_crypto = Param_string ""

let s_strict_alias_mode = "processStrictAliasMode"
let v_strict_alias_mode = Param_bool false

let s_show_strengthened_hyp = "showStrengthenedHyp"
let v_show_strengthened_hyp = Param_bool false

let s_auto_fadup = "autoFADup"
let v_auto_fadup = Param_bool true

let s_new_ind = "newInduction"
let v_new_ind = Param_bool false

let s_post_quantum = "postQuantumSound"
let v_post_quantum = Param_bool false

let s_prettyprint_reify = "prettyPrintReify"
let v_prettyprint_reify = Param_bool true

let init_params (table:Symbols.table) : Symbols.table =
  table
  |> declare s_timeout               v_timeout 
  |> declare s_interactive           v_interactive
  |> declare s_print_equ             v_print_equ
  |> declare s_debug_constr          v_debug_constr
  |> declare s_debug_completion      v_debug_completion
  |> declare s_debug_tactics         v_debug_tactics
  |> declare s_strict_alias_mode     v_strict_alias_mode
  |> declare s_show_strengthened_hyp v_show_strengthened_hyp
  |> declare s_auto_fadup            v_auto_fadup
  |> declare s_new_ind               v_new_ind
  |> declare s_post_quantum          v_post_quantum
  |> declare s_verbose_crypto        v_verbose_crypto
  |> declare s_log_unsat_crypto      v_log_unsat_crypto
  |> declare s_prettyprint_reify     v_prettyprint_reify

(*------------------------------------------------------------------*)
let get_int s table : int =
  let s = L.mk_loc L._dummy s in
  let ns = Symbols.Config.convert_path ([], s) table in
  match as_data (Symbols.Config.get_data ns table) with
  | Param_int i -> i
  | _ -> assert false

let get_bool s table : bool =
  let s = L.mk_loc L._dummy s in
  let ns = Symbols.Config.convert_path ([], s) table in
  match as_data (Symbols.Config.get_data ns table) with
  | Param_bool i -> i
  | _ -> assert false

let get_string s table : string =
  let s = L.mk_loc L._dummy s in
  let ns = Symbols.Config.convert_path ([], s) table in
  match as_data (Symbols.Config.get_data ns table) with
  | Param_string s -> s
  | _ -> assert false

(*------------------------------------------------------------------*)
let solver_timeout          = get_int    s_timeout
let print_trs_equations     = get_bool   s_print_equ
let interactive             = get_bool   s_interactive
let debug_constr            = get_bool   s_debug_constr
let debug_completion        = get_bool   s_debug_completion
let debug_tactics           = get_bool   s_debug_tactics
let strict_alias_mode       = get_bool   s_strict_alias_mode
let show_strengthened_hyp   = get_bool   s_show_strengthened_hyp
let auto_fadup              = get_bool   s_auto_fadup
let new_ind                 = get_bool   s_new_ind
let post_quantum            = get_bool   s_post_quantum
let verbose_crypto          = get_bool   s_verbose_crypto
let log_unsat_crypto        = get_string s_log_unsat_crypto
let prettyprint_reify       = get_bool   s_prettyprint_reify
