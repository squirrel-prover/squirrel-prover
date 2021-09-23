(** Module instantiating the printing interface of Squirrel.
  * It provides printing functions that behave accordingly with
  * the running mode and the kind of printed information. *)

open Format
open Fmt
 
(** Keyword type **)

type keyword = [
  | `ProcessName      (* [reader], [tag], [null] *)
  | `ProcessVariable  (* [x] in [in(cT,x)] *)
  | `ProcessCondition (* [if], [then], [else] *)
  | `ProcessInOut     (* [in], [out] *)
  | `Macro            (* [cond], [happens] *)
  | `Action           (* [R(j)], [T(i,k)] *)
  | `Function         (* [h], [fst], [snd] *)
  | `Name             (* [key], [nT] *)
  | `Channel          (* [cT] *)
  | `Separation       (* [------------] *)
  | `HelpType         (* [Logical tactics:] *)
  | `HelpFunction     (* [admit], [euf] *)
  | `Test
]

(* Each keyword is associated to a unique string
   to be used in semantic tags *)
let kw_id (keyword : keyword) : string = 
  match keyword with
  | `ProcessName -> "pn"
  | `ProcessVariable -> "pv"
  | `ProcessCondition -> "pc"
  | `ProcessInOut -> "pio"
  | `Macro -> "m"
  | `Action -> "a"
  | `Function -> "f"
  | `Name -> "n"
  | `Channel -> "c"
  | `Separation -> "sep"
  | `HelpType -> "ht"
  | `HelpFunction -> "hf"
  | `Test -> "t"

let kw_stag_to_t (stag : stag) : keyword =
  match stag with
  | String_tag("pn") -> `ProcessName
  | String_tag("pv") -> `ProcessVariable
  | String_tag("pc") -> `ProcessCondition
  | String_tag("pio") -> `ProcessInOut
  | String_tag("m") -> `Macro
  | String_tag("a") -> `Action
  | String_tag("f") -> `Function
  | String_tag("n") -> `Name
  | String_tag("c") -> `Channel
  | String_tag("sep") -> `Separation
  | String_tag("ht") -> `HelpType
  | String_tag("hf") -> `HelpFunction
  | String_tag("t") -> `Test
  | _ -> raise Not_found


(** Semantic tag functions **)
(* These functions are used to initialize the printer *)

  (** ANSI **)

(* Each keyword is associated to an ANSI code *)
let kw_ansi (keyword : keyword) : string =
  match keyword with
  | `ProcessName -> "1;34"
  | `ProcessVariable -> "1;35"
  | `ProcessCondition -> "4;31"
  | `ProcessInOut -> "1"
  | `Macro -> "1;35"
  | `Action -> "32"
  | `Function -> "1"
  | `Name -> "33"
  | `Channel -> ""
  | `Separation -> "1"
  | `HelpType -> "1;31"
  | `HelpFunction -> "1;35"
  | `Test -> "1;3;4;35"

(* Defines the string that will be outputed when a semantic tag is opened *)
let kw_ansi_pref (stag : Format.stag) : string =
  "\x1B[" ^ (kw_ansi @@ kw_stag_to_t stag) ^ "m"

(* Defines the string that will be outputed when a semantic tag is closed *)
let kw_ansi_suf (stag : Format.stag) : string =
  "\x1B[0m"

let kw_ansi_stag_funs : Format.formatter_stag_functions = 
  { mark_open_stag = kw_ansi_pref;
    mark_close_stag = kw_ansi_suf;
    print_open_stag = (fun _ -> ());
    print_close_stag = (fun _ -> ()); }

  (** HTML **)

(* Each keyword is associated to HTML attributes *)
let kw_html_attributes (keyword : keyword) : string =
  match keyword with
  | `ProcessName -> " style=\"font-weight:bold; color: #0000AA\""
  | `ProcessVariable -> " style=\"font-weight: bold; color: #AA00AA\""
  | `ProcessCondition -> " style=\"text-decoration: underline; color: #AA0000\""
  | `ProcessInOut -> " style=\"font-weight: bold\""
  | `Macro -> " style=\"font-weight: bold; color: #AA00AA\""
  | `Action -> " style=\"color: #00AA00\""
  | `Function -> " style=\"font-weight: bold\""
  | `Name -> " style=\"color: #AA5500\""
  | `Channel -> ""
  | `Separation -> " style=\"font-weight: bold\""
  | `HelpType -> " style=\"font-weight: bold; color: #AA0000\""
  | `HelpFunction -> " style=\"font-weight: bold; color: #AA00AA\""
  | `Test -> ""

(* Defines the string that will be outputed when a semantic tag is opened *)
let kw_html_pref (stag : Format.stag) : string =
  let ty = kw_stag_to_t stag in
  "<span class=\"" ^ (kw_id ty) ^ "\"" ^ (kw_html_attributes ty) ^ ">"

(* Defines the string that will be outputed when a semantic tag is closed *)
let kw_html_suf (stag : Format.stag) : string =
  "</span>"

let kw_html_stag_funs : Format.formatter_stag_functions = 
  { mark_open_stag = kw_html_pref;
    mark_close_stag = kw_html_suf;
    print_open_stag = (fun _ -> ());
    print_close_stag = (fun _ -> ()); }
  

(** Set printer **)

type printer_mode =
  | Test
  | Html
  | Interactive
  | File

let printer_mode = ref File

(* Initialisation of the printer giving it a mode *)
let init (mode : printer_mode) : unit =
  printer_mode := mode;
  match mode with
  | File | Interactive ->
      Fmt.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
      Format.pp_set_mark_tags Fmt.stdout true;
      pp_set_formatter_stag_functions Fmt.stdout kw_ansi_stag_funs ;
  | Html -> 
      Fmt.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
      Format.pp_set_mark_tags Fmt.stdout true;
      pp_set_formatter_stag_functions Fmt.stdout kw_html_stag_funs ;
  | Test -> ()


(** Printing functions **)

let strf = Fmt.strf

let dummy_fmt = Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())

(* while not currently used, this part provides support for multiple kind
   of outputs *)
let get_std () =
  match !printer_mode with
  | File -> Fmt.stdout
  | Interactive -> Fmt.stdout
  | Html -> Fmt.stdout
  | Test -> Fmt.stdout

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
  | `Result  -> pr "@[[result> "
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

let kw (keyword : keyword) ppf fmt =
  Fmt.pf ppf "@{<%s>" (kw_id keyword);
  Fmt.kpf (fun fmt -> Fmt.pf ppf "@}") ppf fmt

let kws (keyword : keyword) ppf (s : string) =
  kw keyword ppf "%s" s
