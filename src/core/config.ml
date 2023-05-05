(*------------------------------------------------------------------*)
type [@warning "-37"] param_kind =
  | PBool
  | PString
  | PInt

type p_param_val =
  | Param_bool   of bool
  | Param_string of string
  | Param_int    of int

type p_set_param = string * p_param_val

module M = Utils.Ms

let [@warning "-32"] get_int = function _,_, Param_int i -> i | _ -> assert false

let [@warning "-32"] get_string = function 
  | _,_, Param_string s -> s 
  | _ -> assert false

let get_bool = function _,_, Param_bool b -> b | _ -> assert false

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

let s_debug_constr = "debugConstr"
let v_debug_constr = Param_bool false

let s_debug_completion = "debugCompletion"
let v_debug_completion = Param_bool false

let s_debug_tactics = "debugTactics"
let v_debug_tactics = Param_bool false

let s_old_completion = "oldCompletion"
let v_old_completion = Param_bool false

(*------------------------------------------------------------------*)
(** Default parameters values.
    Add one line for each new parameter. *)
let default_params =
      decl s_debug_constr PBool v_debug_constr M.empty
  |>  decl s_debug_completion PBool v_debug_completion
  |>  decl s_debug_tactics PBool v_debug_tactics
  |>  decl s_old_completion PBool v_old_completion

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

let debug_constr     () = get_bool (M.find s_debug_constr !params)
let debug_completion () = get_bool (M.find s_debug_completion !params)
let debug_tactics    () = get_bool (M.find s_debug_tactics !params)


(* FIXME seems to be used once for a test … *)
let old_completion () = get_bool (M.find s_old_completion !params)

let pp_kind fmt = function
  | PBool -> Fmt.pf fmt "bool"
  | PString -> Fmt.pf fmt "string"
  | PInt -> Fmt.pf fmt "int"

(*------------------------------------------------------------------*)
(** {2 set functions} *)

let set_param (s,p) : [`Failed of string | `Success] =
  match M.find s !params with
  | (kind, check, _) ->
    if not (check_kind kind p) then
      `Failed (
        Fmt.str "bad parameter kind: %s expects a %a"
          s pp_kind kind
      )
    else if not (check p) then
      `Failed (Fmt.str "parameter invalid for %s" s)
    else
      begin
        params := M.add s (kind, check, p) !params;
        `Success;
      end

  | exception Not_found -> 
    `Failed (Fmt.str "unknown option %s" s)
