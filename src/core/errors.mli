(** {1 User errors}

    This module allows to define pretty-printers for user-targetted
    exceptions. It is similar to [Printexc] but registering an exception
    here informs us that it is a user-targetted exception, which can be
    raised in the course of using Squirrel --- it is not an anomaly that
    should be reported to developpers. *)

(** Currently an exception is user-targetted if it has a handler,
    and exception information is just a user-friendly pretty-printer for it.
    The printer is parameterized by a location printer.
    Info may be enriched in the future e.g. with more semantic information
    about the exception. *)
type printer =
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> unit
type info = {
  printer : printer
}

val register : (exn -> info option) -> unit

val is_user_error : exn -> bool

(** Pretty-print a user error. In case the exception is not a user error,
    it is pretty-printed as an anomaly (asking the user to report it to the
    devs). *)
val pp_user_error :
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> exn -> unit

(** Tell if tool is in user mode, meaning that errors are reported
    in a user-friendly manner. The opposite of user mode is developper
    mode, better for debugging, where errors are printed using Printexc
    and backtraces are produced.
    In addition to relying on the interactive and (probably historical
    and redundant) test flags from the main loop,
    we use `OCAMLRUNPARAM`: if it contains `b` then user mode is disabled. *)
val user_mode : interactive:bool -> test:bool -> bool
