type cmd_error =
  | UnexpectedCommand
  | AbortIncompleteProof
  | InvalidExtension  of string
  | FileNotFound      of string
  | StartProofError   of string
  | InvalidTheoryName of string
  | IncludeCycle      of string
  | IncludeNotFound   of string * (string list)
  | IncludeFailed     of (Format.formatter -> unit)
  | InvalidSetOption  of string

exception Cmd_error of cmd_error

let pp_error_i fmt = function
  | UnexpectedCommand    -> Fmt.pf fmt "Unexpected command."

  | StartProofError s    -> Fmt.pf fmt "%s" s

  | FileNotFound s       -> Fmt.pf fmt "File %s.sp not found" s

  | AbortIncompleteProof -> Fmt.pf fmt "Trying to abort a completed proof."

  | InvalidTheoryName s  -> Fmt.pf fmt "Invalid theory name %s." s

  | IncludeCycle s       -> Fmt.pf fmt "Include cycle (%s)." s

  | IncludeNotFound (s, paths) ->
    Fmt.pf fmt
      "@[<v 0>Could not locate theory %s.@;\
       @[<v 2>I looked in@ %a@]@]"
      s (Fmt.list Fmt.string) paths

  | InvalidExtension s   -> Fmt.pf fmt "Invalid extension (not a .sp): %s." s

  | IncludeFailed err    -> Fmt.pf fmt "%t" err

  | InvalidSetOption s   -> Fmt.pf fmt "Set failed: %s." s

let pp_error pp_loc_error fmt e =
  let loc = Location._dummy in  (* FIXME: provide useful error location *)
  Fmt.pf fmt "%a%a"
    pp_loc_error loc
    pp_error_i e

let cmd_error e = raise (Cmd_error e)

let () =
  Errors.register (function
    | Cmd_error e ->
        Some { printer =
          fun pp_loc_error fmt -> pp_error pp_loc_error fmt e }
    | _ -> None)
