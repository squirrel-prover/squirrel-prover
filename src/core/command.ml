type cmd_error =
  | UnexpectedCommand
  | AbortIncompleteProof
  | InvalidExtension  of string
  | FileNotFound      of string
  | StartProofError   of string
  | InvalidTheoryName of string
  | IncludeCycle      of string
  | IncludeNotFound   of string
  | IncludeFailed     of (Format.formatter -> unit)
  | InvalidSetOption  of string

exception Cmd_error of cmd_error

let pp_cmd_error fmt = function
  | UnexpectedCommand    -> Fmt.pf fmt "Unexpected command."

  | StartProofError s    -> Fmt.pf fmt "%s" s

  | FileNotFound s       -> Fmt.pf fmt "File %s.sp not found" s

  | AbortIncompleteProof -> Fmt.pf fmt "Trying to abort a completed proof."

  | InvalidTheoryName s  -> Fmt.pf fmt "Invalid theory name %s." s

  | IncludeCycle s       -> Fmt.pf fmt "Include cycle (%s)." s

  | IncludeNotFound s    -> Fmt.pf fmt "Could not locate theory %s." s

  | InvalidExtension s   -> Fmt.pf fmt "Invalid extension (not a .sp): %s." s

  | IncludeFailed err    -> Fmt.pf fmt "%t" err

  | InvalidSetOption s   -> Fmt.pf fmt "Set failed: %s." s

let cmd_error e = raise (Cmd_error e)
