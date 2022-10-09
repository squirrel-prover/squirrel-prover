(** Global variables used in the module *)
(*Output channel to write in the output file*)
let current_out_c = ref stdout
(*Formatter to write in the output file*)
let current_ppf = ref Format.std_formatter
(*Memorize the position of the "<!--HERE-->" tag in the template *)
let tag_pos = ref (-1)
(*Lexer for the input file*)
let lex = ref (Lexing.from_channel stdin)
(*Count the number of instructions treated*)
let counter = ref 0


(** Return [s] without empty lines at the beginnig *)
let trim (s : string) : string =
  let l = String.length s in
  let rec start_pos (pos : int) (start : int): int =
  (* [start] store the position of the begin of a line.
     This value is retuned when a non empty character is read. *)
    if pos >= l then
      pos
    else match s.[pos] with
    | '\n' -> start_pos (pos+1) (pos+1)
    | ' ' | '\x0C' | '\r' | '\t' ->
      start_pos (pos+1) start
    | _ -> start
  in
  let pos = start_pos 0 0 in
  String.sub s pos (l-pos)


(** Print string [s], translating markdown into html
    Use pandoc *)
let print_pandoc ppf (s : string) : unit =
  (*Write s into a first pipe*)
  let (pipe_out, pipe_in) = Unix.pipe() in
  let c_pipe_in = Unix.out_channel_of_descr pipe_in in
  output_string c_pipe_in s ;
  close_out c_pipe_in ;
  
  (*Write the result of pandoc into a second pipe*)
  let (result_out, result_in) = Unix.pipe() in
  let _ = Unix.create_process "pandoc" 
    [|"pandoc" ; "-f" ; "markdown" ; "-t" ; "html"|]
    pipe_out result_in Unix.stderr
  in
  Unix.close pipe_out;
  Unix.close result_in;
  
  (*Print the output of the second pipe*)
  let c_result = Unix.in_channel_of_descr result_out in
  try
    while true do
      let line = input_line c_result in
      Format.fprintf ppf "%s\n" line
    done
  with
  | End_of_file -> close_in c_result


(** Print the output formatted with html tag
  * Input and comments are read in [!lex]
  * Output must be already stored in the standard buffer (standard output for Html printer mode).*)
let pp () =
  let (input_line, coms) = HtmlParser.main HtmlLexer.token !lex in
  let concat_com = String.concat "\n\n" coms in
  let trimed_input_line = if concat_com <> "" then trim input_line else input_line in
  let output_line = (Format.flush_str_formatter ()) in
  (*Open a span element to encapsulated everything*)
  Format.fprintf !current_ppf
    "<span class=\"squirrel-step\" id=\"step%d\">\n"
    !counter;
  (*Print input lines*)
  Format.fprintf !current_ppf
    "<span class=\"input-line\" id=\"in%d\">%a</span>\n"
    !counter
    (Printer.html Format.pp_print_string) trimed_input_line;
  (*Print output lines
    Since they passed throught the str_formatter, they already have an HTML format*)
  Format.fprintf !current_ppf
    "<span class=\"output-line\" id=\"out%d\">%a</span>\n"
    !counter
    Format.pp_print_string output_line;
  (*Print comments, if there are some*)
  if concat_com <> "" then
    Format.fprintf !current_ppf
      "<span class=\"com-line\" id=\"com%d\">%a</span>\n"
      !counter
      print_pandoc concat_com;
  (*Close the span element*)
  Format.fprintf !current_ppf "</span>\n\n";
  incr counter


(** Initialise this module.
  * Input:
  * - [filename]: Name of the squirrel file 
  * - [html_filename]: Name of the html template
  * Effect:
  * - Open a new input channel to read the squirrel file
  * - Create the output file, open a channel toward it and write the first part of the template.*)
let init (filename : string) (html_filename : string) : unit =
  let out_filename = Format.sprintf "%s/%s.html"
    (Filename.dirname html_filename)
    (Filename.(remove_extension @@ basename filename))
  in
  let out_c = open_out out_filename in
  let html_c = open_in html_filename in
  try
    while !tag_pos = -1 do
      let line = input_line html_c in
      if line = "<!--HERE-->" then begin
        tag_pos := pos_in html_c;
      end
      else
        output_string out_c (line ^ "\n")
    done;
    close_in html_c;
    current_out_c := out_c;
    current_ppf := Format.formatter_of_out_channel out_c;
    Format.fprintf !current_ppf "<span style=\"display: none;\">";
    
    let in_c = Stdlib.open_in filename in
    lex := Lexing.from_channel in_c
    
  with
    | End_of_file ->
      Fmt.epr
        "No line \"<!--HERE-->\" in %s\nDeleting %s\nExiting\n"
        html_filename
        out_filename;
      close_in html_c;
      close_out out_c;
      Sys.remove out_filename;
      exit 1


(** End the output:
  * Input:
  * - [html_filename]: Name of the html template
  * Effect:
  * - Write the last part of the template
  * - Close channels opened by this module*)
let close (html_filename : string) : unit =
  Format.fprintf !current_ppf "</span>";
  let html_c = open_in html_filename in
  seek_in html_c !tag_pos;
  try
    while true do
      let line = input_line html_c in
      Format.fprintf !current_ppf "%s\n" line
    done;
  with
    | End_of_file ->
      close_in html_c;
      close_out !current_out_c;
      current_out_c := stdout;
      current_ppf := Format.std_formatter;
      tag_pos := -1
