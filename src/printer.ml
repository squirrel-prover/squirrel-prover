(** Module instantiating the printing interface of Squirrel.
  * It provides printing functions that behave accordingly with
  * the running mode and the kind of printed information. *)

open Format
open Fmt

(** Printer modes *)

type printer_mode =
  | Test
  | Interactive
  | File
  | Html

let printer_mode = ref File

let dummy_fmt = Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())

let get_std () =
  match !printer_mode with
  | File -> Fmt.stdout
  | Interactive -> Fmt.stdout
  | Html -> Format.str_formatter
  | Test -> Fmt.stdout

(** Keywords **)

(* Keyword type *)
type keyword = [
  | `TermCondition    (* [if], [try find], [else] *)
  | `TermDiff         (* [diff] *)
  | `TermSeq          (* [seq] *)
  | `TermHappens      (* [happens] *)
  | `TermBool         (* [true], [false] *)
  | `TermQuantif      (* [forall], [exists] *)
  | `TermAction       (* [init], [pred] *)
  | `ProcessName      (* [reader], [tag], [null] *)
  | `ProcessVariable  (* [x] in [in(cT,x)] *)
  | `ProcessCondition (* [if], [find], [else] *)
  | `ProcessInOut     (* [in], [out] *)
  | `ProcessChannel   (* [cT] *)
  | `ProcessKeyword   (* [let], [set], [new] *)
  | `GoalMacro        (* [cond], [happens] *)
  | `GoalAction       (* [R(j)], [T(i,k)] *)
  | `GoalFunction     (* [h], [fst], [snd] *)
  | `GoalName         (* [key], [nT] *)
  | `Separation       (* [------------] *)
  | `HelpType         (* [Logical tactics:] *)
  | `HelpFunction     (* [admit], [euf] *)
  | `Test             (* May be used to debug *)
  | `Error            (* Used by Match module *)
]


(** Semantic tag functions **)
(* These functions are used to initialize the printer *)

(* Define new types of semantic tags *)
type stag +=
  | Keyword_tag of keyword


  (** ANSI **)

(* Store a pile of ansi_code.
   Used if several styling are intertwined.
   Currently, only used for background color *)
let bg_pile = ref ["0"]

(* Each keyword is associated to an ANSI code *)
let kw_ansi (keyword : keyword) : string =
  match keyword with
  | `TermCondition -> ""
  | `TermDiff -> ""
  | `TermSeq -> ""
  | `TermHappens -> ""
  | `TermBool -> ""
  | `TermQuantif -> ""
  | `TermAction -> ""
  | `ProcessName -> "1;34"
  | `ProcessVariable -> "1;35"
  | `ProcessCondition -> "4;31"
  | `ProcessInOut -> "1"
  | `ProcessChannel -> ""
  | `ProcessKeyword -> "1"
  | `GoalMacro -> "1;35"
  | `GoalAction -> "32"
  | `GoalFunction -> "1"
  | `GoalName -> "33"
  | `Separation -> "1"
  | `HelpType -> "1;31"
  | `HelpFunction -> "1;35"
  | `Test -> "1;3;4;35"
  | `Error -> "101"

(* Defines the string that will be outputed when a semantic tag is opened *)
let kw_ansi_pref (stag : Format.stag) : string =
  match stag with
  | Keyword_tag keyword ->
    let ansi_code = kw_ansi keyword in
    let () = match keyword with
    | `Error -> bg_pile := ansi_code :: !bg_pile
    | _ -> ()
    in
    "\x1B[" ^ ansi_code ^ "m"
  | _ -> failwith "Semantic tag not implemented"

(* Defines the string that will be outputed when a semantic tag is closed *)
let kw_ansi_suf (stag : Format.stag) : string =
  match stag with
  | Keyword_tag `Error -> 
    bg_pile := List.tl !bg_pile;
    "\x1B[" ^ (List.hd !bg_pile) ^ "m"
    (* Return to the previous background color *)
  | Keyword_tag _ ->
    "\x1B[22;24;39m"
    (* Remove all styling except background color *)
  | _ -> failwith "Semantic tag not implemented"

let kw_ansi_stag_funs : Format.formatter_stag_functions =
  { mark_open_stag = kw_ansi_pref;
    mark_close_stag = kw_ansi_suf;
    print_open_stag = (fun _ -> ());
    print_close_stag = (fun _ -> ()); }


  (** HTML **)

(* Each keyword is associated to HTML attributes *)
let kw_html_attributes (keyword : keyword) : string =
  match keyword with
  | `TermCondition -> ""
  | `TermDiff -> ""
  | `TermSeq -> ""
  | `TermHappens -> ""
  | `TermBool -> ""
  | `TermQuantif -> ""
  | `TermAction -> ""
  | `ProcessName -> " class=\x1B\"pn\x1B\" style=\x1B\"font-weight:bold; color: #0000AA\x1B\""
  | `ProcessVariable -> " class=\x1B\"pv\x1B\" style=\x1B\"font-weight: bold; color: #AA00AA\x1B\""
  | `ProcessCondition -> " class=\x1B\"pc\x1B\" style=\x1B\"text-decoration: underline; color: #AA0000\x1B\""
  | `ProcessInOut -> " class=\x1B\"pio\x1B\" style=\x1B\"font-weight: bold\x1B\""
  | `ProcessChannel -> " class=\x1B\"pc\x1B\""
  | `ProcessKeyword -> " class=\x1B\"pk\x1B\" style=\x1B\"font-weight: bold\x1B\""
  | `GoalMacro -> " class=\x1B\"gm\x1B\" style=\x1B\"font-weight: bold; color: #AA00AA\x1B\""
  | `GoalAction -> " class=\x1B\"ga\x1B\" style=\x1B\"color: #00AA00\x1B\""
  | `GoalFunction -> " class=\x1B\"gf\x1B\" style=\x1B\"font-weight: bold\x1B\""
  | `GoalName -> " class=\x1B\"gn\x1B\" style=\x1B\"color: #AA5500\x1B\""
  | `Separation -> " class=\x1B\"sep\x1B\" style=\x1B\"font-weight: bold\x1B\""
  | `HelpType -> " class=\x1B\"ht\x1B\" style=\x1B\"font-weight: bold; color: #AA0000\x1B\""
  | `HelpFunction -> " class=\x1B\"hf\x1B\" style=\x1B\"font-weight: bold; color: #AA00AA\x1B\""
  | `Test -> ""
  | `Error -> " class=\x1B\"err\x1B\" style=\x1B\"background-color: red\x1B\""

(* Defines the string that will be outputed when a semantic tag is opened *)
let kw_html_pref (stag : Format.stag) : string =
  match stag with
  | Keyword_tag keyword ->
    "\x1B<span" ^ (kw_html_attributes keyword) ^ "\x1B>"
  | _ -> failwith "Semantic tag not implemented"


(* Defines the string that will be outputed when a semantic tag is closed *)
let kw_html_suf (stag : Format.stag) : string =
  match stag with
  | Keyword_tag _ ->
    "\x1B</span\x1B>"
  | _ -> failwith "Semantic tag not implemented"

(* Object containing all semantic tag functions for html output *)
let kw_html_stag_funs : Format.formatter_stag_functions =
  { mark_open_stag = kw_html_pref;
    mark_close_stag = kw_html_suf;
    print_open_stag = (fun _ -> ());
    print_close_stag = (fun _ -> ()); }


(** Formatter out functions **)

  (** ANSI **)

(* Another function to assure that all styling stops if the formatter is flushed *)
let ansi_out_funs =
  let base_funs = pp_get_formatter_out_functions (get_std ()) () in
  { out_string = base_funs.out_string ;
    out_flush = (fun () ->
      base_funs.out_string "\x1B[0m" 0 4;
      base_funs.out_flush ()) ;
    out_newline = base_funs.out_newline ;
    out_spaces = base_funs.out_spaces ;
    out_indent = base_funs.out_indent ; }


(** Printer initialization **)


(* Initialisation of the printer giving it a mode *)
let init (mode : printer_mode) : unit =
  printer_mode := mode;
  match mode with
  | File | Interactive ->
      Fmt.set_style_renderer
        (get_std ()) `Ansi_tty;
      Format.pp_set_mark_tags
        (get_std ()) true;
      pp_set_formatter_stag_functions
        (get_std ()) kw_ansi_stag_funs ;
      pp_set_formatter_out_functions
        (get_std ()) ansi_out_funs
  | Html ->
      Format.pp_set_mark_tags (get_std ()) true;
      pp_set_formatter_stag_functions
        (get_std ()) kw_html_stag_funs
  | Test -> ()


(** {2 Printing functions} **)

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

let kw (keyword : keyword) ppf fmt =
  Format.pp_open_stag ppf (Keyword_tag keyword);
  Fmt.kpf (fun ppf -> Format.pp_close_stag ppf ()) ppf fmt

let kws (keyword : keyword) ppf (s : string) =
  kw keyword ppf "%s" s
