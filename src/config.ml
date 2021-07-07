(*------------------------------------------------------------------*)
(* parser types *)

type p_param_val =
  | Param_bool   of bool
  | Param_string of string
  | Param_int    of int     

type p_set_param = string * p_param_val

(*------------------------------------------------------------------*)
(* parameter type *)
                   
module M = Utils.Ms

type param_kind =
  | PBool
  | PString
  | PInt

let pp_kind fmt = function
  | PBool -> Fmt.pf fmt "bool"
  | PString -> Fmt.pf fmt "string"
  | PInt -> Fmt.pf fmt "int"

  
let get_int    = function _,_, Param_int    i -> i | _ -> assert false
let get_string = function _,_, Param_string s -> s | _ -> assert false
let get_bool   = function _,_, Param_bool   b -> b | _ -> assert false

(** Function checking that a parameter value is valid.
    To be registered when declaring a new parameter. *)
type check_param = p_param_val -> bool
  
(** Map storing the value of declared parameters. *)
type params = (param_kind * check_param * p_param_val) M.t

let check_kind kind default = match kind, default with
  | PBool, Param_bool _
  | PInt, Param_int _ 
  | PString, Param_string _ -> true
  | _ -> false
    
(*------------------------------------------------------------------*)
(** {2 declaration of new parameters} *)

let decl name kind ?check default (params : params) =
  if M.mem name params then
    raise (Invalid_argument "Declared an already existing parameter.")
  else
    let () = assert (check_kind kind default) in
    let check = match check with
      | None -> fun _ -> true
      | Some f -> f in
    M.add name (kind,check, default) params

(*------------------------------------------------------------------*)
(** list of parameters strings (to be set in *.sp files) and 
   default value. *)

let s_timeout = "timeout"
let v_timeout = Param_int 2
let check_timeout = function
  | Param_int 0 -> Printer.prt `Error "Timeout must strictly positive"; false
  | _ -> true
  
let s_print_equ = "printTRSEquations"
let v_print_equ = Param_bool false

let s_debug_constr = "debugConstr"
let v_debug_constr = Param_bool false

let s_debug_completion = "debugCompletion"
let v_debug_completion = Param_bool false

let s_debug_tactics = "debugTactics"
let v_debug_tactics = Param_bool false

let s_strict_alias_mode = "processStrictAliasMode"
let v_strict_alias_mode = Param_bool false

let s_show_strengthened_hyp = "showStrengthenedHyp"
let v_show_strengthened_hyp = Param_bool false

let s_auto_intro = "autoIntro"
let v_auto_intro = Param_bool true

let s_auto_fadup = "autoFADup"
let v_auto_fadup = Param_bool true

let s_new_ind = "newInduction"
let v_new_ind = Param_bool false

(*------------------------------------------------------------------*)
(** Default parameters values.
    Add one line for each new parameter. *)
let default_params =
      decl s_timeout ~check:check_timeout PInt v_timeout M.empty 
  |>  decl s_print_equ PBool v_print_equ 
  |>  decl s_debug_constr PBool v_debug_constr 
  |>  decl s_debug_completion PBool v_debug_completion
  |>  decl s_debug_tactics PBool v_debug_tactics
  |>  decl s_strict_alias_mode PBool v_strict_alias_mode
  |>  decl s_show_strengthened_hyp PBool v_show_strengthened_hyp
  |>  decl s_auto_intro PBool v_auto_intro
  |>  decl s_auto_fadup PBool v_auto_fadup
  |>  decl s_new_ind PBool v_new_ind

(*------------------------------------------------------------------*)
(** reference to the current parameters *)
let params = ref default_params

let reset_params () = params := default_params

let get_params () = !params

let set_params p = params := p

(*------------------------------------------------------------------*)
(** {2 look-up functions} *)

let solver_timeout () = get_int (M.find s_timeout !params)

let print_trs_equations () = get_bool (M.find s_print_equ !params)

let debug_constr     () = get_bool (M.find s_debug_constr !params)
let debug_completion () = get_bool (M.find s_debug_completion !params)
let debug_tactics    () = get_bool (M.find s_debug_tactics !params)

let strict_alias_mode () = get_bool (M.find s_strict_alias_mode !params)

let show_strengthened_hyp () = get_bool (M.find s_show_strengthened_hyp !params)
    
let auto_intro () = get_bool (M.find s_auto_intro !params)

let auto_fadup () = get_bool (M.find s_auto_fadup !params)

let new_ind () = get_bool (M.find s_new_ind !params) 

(*------------------------------------------------------------------*)
(** {2 set functions} *)

let set_param (s,p) =
  match M.find s !params with
  | (kind, check, _) ->
    if not (check_kind kind p) then
      Printer.prt `Error "Bad parameter kind: %s expects a %a"
        s pp_kind kind
    else if not (check p) then
      Printer.prt `Error "Parameter invalid for %s" s
    else params := M.add s (kind, check, p) !params 
      
  | exception Not_found -> Printer.prt `Error "Unknown option %s" s

