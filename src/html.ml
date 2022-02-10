(** Global variables used in the module *)
(*Output channel to write in the output file*)
let current_out_c = ref stdout
(*Memorize the position of the "<!--HERE-->" tag in the template *)
let tag_pos = ref (-1)
(*Lexer for the input file*)
let lex = ref (Lexing.from_channel stdin)
(*Count the number of instructions treated*)
let counter = ref 0

(** Print [c].
  * Escape it if it is a html reserved character,
  * unless previous character was ESC *)
let print_esc_char (escaping : bool ref) (c : char) : unit =
  if !escaping then begin
    match c with
    | '\x1B' -> escaping := false;
    | '\n' -> output_string !current_out_c "<br>"
    | '<' -> output_string !current_out_c "&lt;"
    | '>' -> output_string !current_out_c "&gt;"
    | '"' -> output_string !current_out_c "&quot;"
    | '&' -> output_string !current_out_c "&amp;"
    | _ -> output_char !current_out_c c
  end
  else begin
    escaping := true;
    output_char !current_out_c c
  end

(** Print [s].
  * Escape html reserved characters *)
let print_esc_string (s : string) : unit =
  String.iter (print_esc_char (ref true)) s

(** Print string [s], translating markdown into html
    Use pandoc *)
let print_pandoc (s : string) : unit =
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
      output_string !current_out_c line ;
      output_char !current_out_c '\n'
    done
  with
  | End_of_file -> close_in c_result

(** Print the output formatted with html tag
  * Input and comments are read in [!lex]
  * Output must be already stored in the standard buffer (standard output for Html printer mode).*)
let pp () =
  let (input_line, coms) = HtmlParser.main HtmlLexer.token !lex in
  let concat_com = String.concat "\n" coms in
  
  output_string !current_out_c (Format.asprintf 
    "<span class=\"squirrel-step\" id=\"step%d\">\n"
    !counter);
  
  (*Print input lines*)
  output_string !current_out_c (Format.asprintf 
    "<span class=\"input-line\" id=\"in%d\">"
    !counter);
  if concat_com <> "" then
    print_esc_string (String.trim input_line)
  else
    print_esc_string input_line;
  output_string !current_out_c "</span>\n";

  (*Print output lines*)
  output_string !current_out_c (Format.asprintf
    "<span class=\"output-line\" id=\"out%d\">"
    !counter);
  let output_line = (Format.flush_str_formatter ()) in
  print_esc_string output_line;
  output_string !current_out_c "</span>\n";
  
  (*Print comments*)
  if concat_com <> "" then begin
    output_string !current_out_c (Format.asprintf
      "<span class=\"com-line\" id=\"com%d\">"
      !counter);
    print_pandoc concat_com;
    output_string !current_out_c "</span>\n"
  end ;
  
  output_string !current_out_c "</span>\n\n";
  
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
        output_string out_c
          "<span style=\"display: none;\">"
      end
      else
        output_string out_c (line ^ "\n")
    done;
    close_in html_c;
    current_out_c := out_c;
    
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
  output_string !current_out_c "</span>";
  let html_c = open_in html_filename in
  seek_in html_c !tag_pos;
  try
    while true do
      let line = input_line html_c in
      output_string !current_out_c (line ^ "\n")
    done;
  with
    | End_of_file ->
      close_in html_c;
      close_out !current_out_c;
      current_out_c := stdout;
      tag_pos := -1
