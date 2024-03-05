(*------------------------------------------------------------------*)
type p_param_val =
  | Param_bool   of bool
  | Param_string of string
  | Param_int    of int

type p_set_param = string * p_param_val

module M = Utils.Ms

let get_bool = function _, Param_bool b -> b | _ -> assert false

(** Function checking that a parameter value is valid.
    To be registered when declaring a new parameter. *)
type check_param = p_param_val -> bool

(** Map storing the value of declared parameters. *)
type params = (check_param * p_param_val) M.t

let check_kind kind default = match kind, default with
  | Param_bool   _, Param_bool   _
  | Param_int    _, Param_int    _
  | Param_string _, Param_string _ -> true
  | _ -> false

(*------------------------------------------------------------------*)
(** {2 declaration of new parameters} *)

let decl name ?check default (params : params) =
  if M.mem name params then
    raise (Invalid_argument "Declared an already existing parameter.")
  else
    let check = Utils.odflt (fun _ -> true) check in
    M.add name (check,default) params

(*------------------------------------------------------------------*)
(** list of parameters strings (to be set in *.sp files) and
   default value. *)

let s_debug_constr = "debugConstr"
let v_debug_constr = Param_bool false

let s_debug_completion = "debugCompletion"
let v_debug_completion = Param_bool false

let s_debug_tactics = "debugTactics"
let v_debug_tactics = Param_bool false

(*------------------------------------------------------------------*)
(** Default parameters values.
    Add one line for each new parameter. *)
let default_params =
  M.empty
  |> decl s_debug_constr     v_debug_constr      
  |> decl s_debug_completion v_debug_completion
  |> decl s_debug_tactics    v_debug_tactics

(*------------------------------------------------------------------*)
(** reference to the current parameters *)
let params = ref default_params

(* OK *)
let reset_params () = params := default_params

(* Deprecated when in table TOREMOVE *)
let get_params () = !params

(* Deprecated when in table TOREMOVE *)
let set_params p = params := p

(*------------------------------------------------------------------*)
(** {2 look-up functions} *)

let debug_constr     () = get_bool (M.find s_debug_constr     !params)
let debug_completion () = get_bool (M.find s_debug_completion !params)
let debug_tactics    () = get_bool (M.find s_debug_tactics    !params)

let pp_kind fmt = function
  | `Bool   -> Fmt.pf fmt "bool"
  | `String -> Fmt.pf fmt "string"
  | `Int    -> Fmt.pf fmt "int"

let get_kind = function
  | Param_bool   _ -> `Bool
  | Param_string _ -> `String
  | Param_int    _ -> `Int
    
(*------------------------------------------------------------------*)
(** {2 set functions} *)

let set_param (s,p) : [`Failed of string | `Success] =
  match M.find s !params with
  | (check, old_val) ->
    if not (check_kind old_val p) then
      `Failed (
        Fmt.str "bad parameter kind: %s expects a %a"
          s pp_kind (get_kind old_val)
      )
    else if not (check p) then
      `Failed (Fmt.str "parameter invalid for %s" s)
    else
      begin
        params := M.add s (check, p) !params;
        `Success;
      end

  | exception Not_found -> 
    `Failed (Fmt.str "unknown option %s" s)
