(** Module instantiating the printing interface of Squirrel.
    It provides printing functions that behave accordingly with
    the running mode and the kind of printed information. *)

open Utils
    
(** {2 Keywords} *)

(** Keyword type. *)
type keyword = [ 
  | `TermCondition
  | `TermDiff
  | `TermSeq
  | `TermHappens
  | `TermBool
  | `TermQuantif
  | `TermAction
  | `ProcessName
  | `ProcessVariable
  | `ProcessCondition
  | `Goal
  | `Prog
  | `ProcessInOut
  | `ProcessChannel
  | `ProcessKeyword
  | `GoalMacro
  | `GoalAction
  | `GoalFunction
  | `GoalName
  | `Separation
  | `HelpType
  | `HelpFunction
  | `Test
  | `Error
]


(** {2 Printer initialization} *)

type printer_mode = Test | Interactive | File | Html | Js

(** Current printer_mode. *)
val printer_mode : printer_mode ref

(** A formatter that does not print anything. *)
val dummy_fmt : Format.formatter

(** Define a standard formatter for the printer w.r.t. printer_mode. *)
val get_std : unit -> Format.formatter

(** Initialisation of a formatter. *)
val init_ppf : printer_mode formatter

(** Initialisation of the standard formatter. *)
val init : printer_mode -> unit


(** {2 Printing functions} *)

(** Type defining the markup to use before and after printing. *)
type pp = [ `Prompt | `Start | `Result | `Error
          | `Dbg | `Warning | `Ignore | `Goal | `Default
          | `Vbs]

(** Print with the printer's standard formatter w.r.t. a given markup. *)
val prt : pp -> ('a, Format.formatter, unit) format -> 'a

(** Print for html with the printer's standard formatter w.r.t. a given markup. *)
val prthtml : pp -> ('a, Format.formatter, unit) format -> 'a

(** Print for html with the giver formatter w.r.t. a given markup. *)
val prthtml_out : Format.formatter -> pp -> ('a, Format.formatter, unit) format -> 'a

(** Default printer, look at mode and use either prt or prthml. *)
val defprt : pp -> ('a, Format.formatter, unit) format -> 'a

(** Default printing on the printer's standard formatter. *)
val pr : ('a, Format.formatter, unit) format -> 'a

(** Print the given format with the style associated with the given keyword. *)
val kw : keyword -> Format.formatter -> ('a, Format.formatter, unit) format -> 'a

(** Like [kw] but with a string. *)
val kws : keyword -> Format.formatter -> string -> unit


(** {2 HTML printing} *)

(** [html pp] return a printing function which apply [pp] with HTML tags and escaping special characters *)
val html : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
