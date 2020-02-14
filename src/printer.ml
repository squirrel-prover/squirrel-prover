(** Module instantiating the printing interface of MetaBC.
    It is the basis of a clean API for the tool.
    Depending on the running mode and the kind of printed information,
    it implements the printing functions.
*)
include Fmt

type printer_mode =
  | Test
  | Interactive
  | File

let printer_mode = ref File

let dummy_fmt =  Format.make_formatter
      (fun _ _ _ -> ())
      (fun () -> ())

let pr =
  match !printer_mode with
  | File -> Fmt.pr
  | Interactive -> Fmt.pr
  | Test -> Fmt.pf dummy_fmt

type pp =
  [ `Prompt
  | `Start
  | `Result
  | `Error
  | `Goal
  | `Default]

let pp ty s =
  match ty with
  | `Prompt -> pr "@[[> %s@.@]@." s
  | `Start -> pr "@[[start> %s@.@]@." s
  | `Result -> pr "@[[result> %s@.@]@." s
  | `Error -> pr "@[[error> %s@.@]@." s
  | `Goal -> pr "@[[goal> %s@.@]@." s
  | `Default -> pr "%s" s

let prt ty fmt = Fmt.kstrf (pp ty) fmt

let pr fmt = Fmt.kstrf (pp `Default) fmt


let set_style_renderer =
    match !printer_mode with
  | File -> Fmt.set_style_renderer
  | Interactive -> Fmt.set_style_renderer
  | Test -> fun _ _  -> ()
