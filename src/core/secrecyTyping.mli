(** This module extends Symbols.stype to define security types,
    and provides operations on these types.
    Implements the work published in:
      Secrecy by typing in the computational model,
      Stéphanie Delaune, Clément Herouard, Joseph Lallemand
      CSF 2025 *)

(** {2 Secrecy types} *)
(** Defintion of security types.
    Extension of [Symbols.stype] *)

(** Export some types. *)
val high : Symbols.stype (*Secret term*)
val low : Symbols.stype (*Public term*)
val boolean : Symbols.stype (*Boolean term*)

(** {2 Pretty-printing} *)

val pp : Format.formatter -> Symbols.stype -> unit



(** {2 Error handling} *)
(** Error declarations and printing *)

(** {3 Typing errors} *)
(** Errors that can happen when declaring a type.
    These errors do not create failures when declaring a system,
    but are intended to bring feedback to the user. *)
type typing_error

val pp_error : Format.formatter -> typing_error -> unit

(** {3 Conversion errors} *)
(** Errors that can happens when declaring a type. *)
type conversion_error
exception Conv of conversion_error

val pp_conv_error :
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> conversion_error -> unit



(** {2 Type checking} *)
(** Functions used to type a term or a system. *)

(** Check if the given system is well-typed,
  * i.e. it types each output, condition and macro for each action
  * w.r.t typing information present in the table.
  * Returns [Ok (forms)] if the system is well-typed, and [Error e] otherwise.
    [forms] contains formulas necessary for the typing to be sound. *)
val check_system : Symbols.table -> Projection.t -> Symbols.system ->
  (LowTraceSequent.conc_form list, typing_error) result

(** [check_initial_state table t vars sty] returns [true] if the initial
    term [t] types [sty] in any environment in which [vars] are consts. *)
val check_initial_state :
  Symbols.table -> Term.term -> Vars.vars -> Symbols.stype -> bool

(** [is_type env t sty] returns [Ok (forms)] if the term [t] types [sty] in
    the environment [env]. [forms] contains formulas necessary for the typing
    to be sound.
    Otherwise, returns [Error e]. *)
val is_type : Env.t -> Term.term -> Symbols.stype ->
  (LowTraceSequent.conc_form list, typing_error) result



(** {2 Declaration checks} *)
(** Functions to check type in a name or state declaration *)

(** [check_config table] raises an [Error] exception if
    the setting "securityTypes" is not set to true in [table]. *)
val check_config : Symbols.table -> unit

(** [check_name_type symb sty] raises an [Error] exception if
    type [sty] cannot be given to a name,
    i.e is not Low, High, Rand or a key type. *)
val check_name_type : Symbols.lsymb -> Symbols.stype -> unit

(** [check_state_type symb sty] raises an [Error] exception if
    type [sty] cannot be given to a state,
    i.e is not a message type. *)
val check_state_type : Symbols.lsymb -> Symbols.stype -> unit

(** [check_large_req symb sty ty] raises an [Error] exception if
    [ty] does not have the tag large, and the name type [sty] require this tag,
    i.e [sty] is different than Low. *)
val check_large_req : Symbols.lsymb -> Symbols.stype -> Type.ty -> unit



(** {2 Parsing} *)
(** Data structure to parse security types *)

(** Types for message *)
type message_type_i =
    Msg
  | High
  | Low
  | Cst of Symbols.p_path
  | Bool
  | Sum of message_type_i * message_type_i
  | Prod of message_type_i * message_type_i

(** Type for keys *)
type key_type_i =
    SK of message_type_i * Symbols.p_path
  | AK of message_type_i * Symbols.p_path
  | SSK of message_type_i * Symbols.p_path
  
(** Security types *)
type stype_i =
    Message of message_type_i
  | Key of key_type_i
  | Rand
  | Wrong

(** Convert a security type [sty_i] from the parser into a type from the theory
    with the table [table].
    May raise an [Error] exception. *)
val convert : Symbols.table -> stype_i -> Symbols.stype