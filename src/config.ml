(*------------------------------------------------------------------*)
(* parser types *)

type p_param_val =
  | Param_bool   of bool
  | Param_string of string
  | Param_int    of int     

type p_set_param = string * p_param_val

(*------------------------------------------------------------------*)
(* parameter type *)
                   
module M = Map.Make(String)

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
(* declaration of new parameters *)

let decl name kind ?check default (params : params) =
  if M.mem name params then
    raise (Invalid_argument "Declared an already existing parameter.")
  else
    let () = assert (check_kind kind default) in
    let check = match check with
      | None -> fun _ -> true
      | Some f -> f in
    M.add name (kind,check, default) params

let s_timeout = "timeout"
let v_timeout = Param_int 2
let check_timeout = function
  | Param_int 0 -> Printer.prt `Error "Timeout must strictly positive"; false
  | _ -> true
  
let s_print_equ = "printTRSEquations"
let v_print_equ = Param_bool false


let default_params =
  let params = decl s_timeout ~check:check_timeout PInt v_timeout M.empty in
  decl s_print_equ PBool v_print_equ params

(* reference to the current parameters *)
let params = ref default_params

let get_params () = !params

let set_params p = params := p

(*------------------------------------------------------------------*)
(* look-up functions *)

let solver_timeout () = get_int (M.find s_timeout !params)

let print_trs_equations () = get_bool (M.find s_print_equ !params)

(*------------------------------------------------------------------*)
(* set functions *)

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

