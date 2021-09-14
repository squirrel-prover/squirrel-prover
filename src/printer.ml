(** Module instantiating the printing interface of Squirrel.
  * It provides printing functions that behave accordingly with
  * the running mode and the kind of printed information. *)

open Fmt

type printer_mode =
  | Test
  | Interactive
  | File

let printer_mode = ref File

let strf = Fmt.strf

let dummy_fmt = Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())

(* while not currently used, this part provides support for multiple kind
   of outputs *)
let get_std () =
  match !printer_mode with
  | File -> Fmt.stdout
  | Interactive -> Fmt.stdout
  | Test -> Fmt.stdout

let set_style_renderer x =
    match !printer_mode with
  | File -> Fmt.set_style_renderer x
  | Interactive -> Fmt.set_style_renderer x
  (* in testing, we disable ansi sequences which are not stored proprely by
     alcotest. *)
  | Test -> fun _  -> ()


let pr x = Fmt.pf (get_std ()) x

type pp = [
  | `Prompt
  | `Start
  | `Result
  | `Error
  | `Dbg
  | `Warning
  | `Ignore (* do not print *)
  | `Goal
  | `Default
]

let pp_pref (ty : pp) =
  match ty with
  | `Prompt  -> pr "@[[> "
  | `Start   -> pr "@[[start> "
  | `Result  -> pr "@["
  | `Error   -> pr "@[[error> "
  | `Dbg     -> pr "@[[dbg> "
  | `Warning -> pr "@[[warning> "
  | `Ignore  -> ()
  | `Goal    -> pr "@[[goal> "
  | `Default -> ()

let pp_suf (ty : pp) =
  match ty with
  | `Prompt  -> pr "@;@]@."
  | `Start   -> pr "@;<]@]@."
  | `Result  -> pr "@;@]@."
  | `Error   -> pr "@;@]@."
  | `Dbg     -> pr "@;<]@]@."
  | `Warning -> pr "@;<]@]@."
  | `Ignore  -> ()
  | `Goal    -> pr "@;@]@."
  | `Default -> ()


let prt ty fmt = 
  let out = match ty with
    | `Ignore -> dummy_fmt
    | _ -> get_std () in
    pp_pref ty; Fmt.kpf (fun fmt -> pp_suf ty) out fmt

let pr fmt = prt `Default fmt
