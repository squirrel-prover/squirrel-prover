(** This module permit to write the html output into its file *)

(** Print the output formatted with its html tag
  * - Input and comments are read in [!lex]
  * - Output must be already stored in the standard buffer (standard output for Html printer mode)
  * - Html reserved caracters are escaped, unless they are preceded by a ESC ('\x1B') character
  * - Comments are formated with pandoc *)
val pp : unit -> unit

(** [init filename html_filename] initialise this module.
  
  * Input:
  * - [filename]: Name of the squirrel file
  * - [html_filename]: Name of the html template
  
  * Effect:
  * - Open a new input channel to read the squirrel file
  * - Create the output file, open a channel toward it
  * and write the first part of the template*)
val init : string -> string -> unit

(** [close html_filename] end the html output.
  
  * Input:
  * - [html_filename]: Name of the html template
  
  * Effect:
  * - Write the last part of the template
  * - Close channels opened by this module*)
val close : string -> unit
