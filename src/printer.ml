(** Module instantiating the printing interface of Squirrel.
  * It provides printing functions that behave accordingly with
  * the running mode and the kind of printed information. *)

open Format
open Fmt


(** Keyword type **)

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
  | `Test             (* Used to debug *)
]

type error_keyword = [
  | `Error
  | `Test
]


(** Semantic tag functions **)
(* These functions are used to initialize the printer *)

(*Define new types of semantic tags*)
type stag +=
  | Keyword_tag of keyword
  | Error_tag of error_keyword
  | Input_tag
  | Output_tag


  (** ANSI **)

let bg_pile = ref ["0"]

(* Each keyword is associated to an ANSI code *)
let kw_ansi (keyword : keyword) : string =
  match keyword with
  | `TermCondition -> "31"
  | `TermDiff -> "31"
  | `TermSeq -> "31"
  | `TermHappens -> "31"
  | `TermBool -> "31"
  | `TermQuantif -> "31"
  | `TermAction -> "31"
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

let error_ansi (error_kw : error_keyword) : string =
  match error_kw with
  | `Error -> "101"
  | `Test -> "103"

(* Defines the string that will be outputed when a semantic tag is opened *)
let kw_ansi_pref (stag : Format.stag) : string =
  match stag with
  | Keyword_tag keyword ->
    "\x1B[" ^ (kw_ansi keyword) ^ "m"
  | Error_tag error_kw ->
    let ansi_code = error_ansi error_kw in
    bg_pile := ansi_code :: !bg_pile ;
    "\x1B[" ^ ansi_code ^ "m"
  | Input_tag -> ""
  | Output_tag -> ""
  | _ -> failwith "Semantic tag not implemented"

(* Defines the string that will be outputed when a semantic tag is closed *)
let kw_ansi_suf (stag : Format.stag) : string =
  match stag with
  | Keyword_tag _ ->
    "\x1B[22;24;39m"
  | Error_tag _ -> 
    bg_pile := List.tl !bg_pile;
    "\x1B[" ^ (List.hd !bg_pile) ^ "m"
  | Input_tag -> ""
  | Output_tag -> ""
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
  | `ProcessName -> " class=\"pn\" style=\"font-weight:bold; color: #0000AA\""
  | `ProcessVariable -> " class=\"pv\" style=\"font-weight: bold; color: #AA00AA\""
  | `ProcessCondition -> " class=\"pc\" style=\"text-decoration: underline; color: #AA0000\""
  | `ProcessInOut -> " class=\"pio\" style=\"font-weight: bold\""
  | `ProcessChannel -> " class=\"pc\""
  | `ProcessKeyword -> " class=\"pk\" style=\"font-weight: bold\""
  | `GoalMacro -> " class=\"gm\" style=\"font-weight: bold; color: #AA00AA\""
  | `GoalAction -> " class=\"ga\" style=\"color: #00AA00\""
  | `GoalFunction -> " class=\"gf\" style=\"font-weight: bold\""
  | `GoalName -> " class=\"gn\" style=\"color: #AA5500\""
  | `Separation -> " class=\"sep\" style=\"font-weight: bold\""
  | `HelpType -> " class=\"ht\" style=\"font-weight: bold; color: #AA0000\""
  | `HelpFunction -> " class=\"hf\" style=\"font-weight: bold; color: #AA00AA\""
  | `Test -> ""

let error_html_attributes (error_kw : error_keyword) : string =
  match error_kw with
  | `Error -> " class=\"err\" style=\"background-color: red\""
  | `Test -> ""

(* Defines the string that will be outputed when a semantic tag is opened *)
let kw_html_pref (stag : Format.stag) : string =
  match stag with
  | Keyword_tag keyword ->
    "<span" ^ (kw_html_attributes keyword) ^ ">"
  | Error_tag error_kw -> 
    "<span" ^ (error_html_attributes error_kw) ^ ">"
  | Input_tag -> ""
  | Output_tag -> ""
  | _ -> failwith "Semantic tag not implemented"
  

(* Defines the string that will be outputed when a semantic tag is closed *)
let kw_html_suf (stag : Format.stag) : string =
  match stag with
  | Keyword_tag _ | Error_tag _ ->
    "</span>"
  | Input_tag -> ""
  | Output_tag -> ""
  | _ -> failwith "Semantic tag not implemented"

(* Object containing all semantic tag functions for html output *)
let kw_html_stag_funs : Format.formatter_stag_functions = 
  { mark_open_stag = kw_html_pref;
    mark_close_stag = kw_html_suf;
    print_open_stag = (fun _ -> ());
    print_close_stag = (fun _ -> ()); }


(** Formatter out functions **)

  (** ANSI **)

let ansi_out_funs =
  let base_funs = get_formatter_out_functions () in
  { out_string = base_funs.out_string ;
    out_flush = (fun () ->
      base_funs.out_string "\x1B[0m" 0 4;
      base_funs.out_flush ()) ;
    out_newline = base_funs.out_newline ;
    out_spaces = base_funs.out_spaces ;
    out_indent = base_funs.out_indent ; }


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
      pp_set_formatter_out_functions Fmt.stdout ansi_out_funs
  | Html -> 
      Fmt.set_style_renderer Fmt.stdout Fmt.(`Ansi_tty);
      Format.pp_set_mark_tags Fmt.stdout true;
      pp_set_formatter_stag_functions
        Fmt.stdout kw_html_stag_funs
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

let err_kw error_kw ppf fmt =
  Format.pp_open_stag ppf (Error_tag error_kw);
  Fmt.kpf (fun ppf -> Format.pp_close_stag ppf ()) ppf fmt
