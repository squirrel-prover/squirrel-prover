(** If the variable [SP_VISU] is set to [ok] in the environement,
    launch a local server with port 8080.
    Gives access to:
    - [visualisation.html] which print data on the state of the current proof
    - [dump.json] which contains the data for the visualisation.*)
val start : unit -> unit

(** Send an event [update] to the page.
    Indicates that the data in [dump.json] have changed. *)
val update : Prover.state -> unit
