include Squirrelfront
include Squirrelcore
include Driver

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

(** check if an exception is handled *)
let is_toplevel_error ?(interactive=true) ~test (e : exn) : bool =
  match e with
  | Parserbuf.Error                 _
  | ProverLib.Error                 _
  | Command.Cmd_error               _
  | Process.Error                   _
  | ProcessDecl.Error               _
  | Theory.Conv                     _
  | Symbols.Error                   _
  | System.Error                    _
  | SystemExpr.Error                _
  | Crypto.Parse.Error              _
  | Tactics.Tactic_soft_failure     _
  | Tactics.Tactic_hard_failure     _ -> not test

  | _e when interactive -> not test

  | _ -> false

(** [is_toplevel_error] must be synchronized with [pp_toplevel_error] *)
let pp_toplevel_error
    ?(interactive=true)
    ~test
    (file : file)
    (fmt : Format.formatter)
    (e : exn) : unit
  =
  let pp_loc_error     = pp_loc_error     file in
  let pp_loc_error_opt = pp_loc_error_opt file in

  match e with
  | Parserbuf.Error s ->
    Fmt.string fmt s

  | ProverLib.Error e ->
    ProverLib.pp_error pp_loc_error fmt e

  | Command.Cmd_error e ->
    Command.pp_cmd_error fmt e

  | Process.Error e ->
    (Process.pp_error pp_loc_error) fmt e

  | ProcessDecl.Error e when not test ->
    (ProcessDecl.pp_error pp_loc_error) fmt e

  | Theory.Conv e when not test ->
    (Theory.pp_error pp_loc_error) fmt e

  | Symbols.Error e when not test ->
    (Symbols.pp_error pp_loc_error) fmt e

  | System.Error e when not test ->
    Format.fprintf fmt "System error: %a" System.pp_error e

  | SystemExpr.Error (l,e) when not test ->
    (SystemExpr.pp_error pp_loc_error_opt) fmt (l,e)

  | Crypto.Parse.Error e when not test ->
    Crypto.Parse.pp_error pp_loc_error fmt e

  | Tactics.Tactic_soft_failure (l,e) when not test ->
    Fmt.pf fmt "%aTactic failed: %a"
      pp_loc_error_opt l
      Tactics.pp_tac_error_i e

  | Tactics.Tactic_hard_failure (l,e) when not test ->
    Fmt.pf fmt "%aTactic ill-formed or unapplicable: %a"
      pp_loc_error_opt l
      Tactics.pp_tac_error_i e

  | e when interactive ->
    Fmt.pf fmt "Anomaly, please report: %s" (Printexc.to_string e)
    
  | _ -> assert false


