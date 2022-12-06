type cmd_error =
  | Unexpected_command
  | AbortIncompleteProof
  | InvalidExtention  of string
  | StartProofError   of string
  | InvalidTheoryName of string
  | IncludeCycle      of string
  | IncludeNotFound   of string
  | IncludeFailed     of (Format.formatter -> unit)
  | InvalidSetOption  of string

exception Cmd_error of cmd_error

let pp_cmd_error fmt = function
  | Unexpected_command   -> Fmt.pf fmt "Unexpected command."

  | StartProofError s    -> Fmt.pf fmt "%s" s

  | AbortIncompleteProof -> Fmt.pf fmt "Trying to abort a completed proof."

  | InvalidTheoryName s  -> Fmt.pf fmt "invalid theory name %s" s

  | IncludeCycle s       -> Fmt.pf fmt "include cycle (%s)" s

  | IncludeNotFound s    -> Fmt.pf fmt "could not locate theory: %s" s

  | InvalidExtention s   -> Fmt.pf fmt "invalid extention (not a .sp): %s" s

  | IncludeFailed err    -> Fmt.pf fmt "%t" err

  | InvalidSetOption s   -> Fmt.pf fmt "set failed: %s" s

let cmd_error e = raise (Cmd_error e)
