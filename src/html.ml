let current_out_c = ref stdout
let tag_pos = ref (-1)
let lex = ref (Lexing.from_channel stdin)

(** Print [c].
  * Escape it if it is a html reserved character,
  * unless previous character was ESC *)
let esc_char (escaping : bool ref)(c : char) : unit =
  if !escaping then begin
    match c with
    | '\x1B' -> escaping := false;
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



(** Input *)

let () = ()

(** Printing of html output *)
let pp in_chan p1 p2 counter =
  (*Print input lines*)
  let (input_line, coms) = HtmlParser.main HtmlLexer.token !lex in
  output_string !current_out_c (Format.asprintf 
    "<span class=\"input-line\" id=\"in%d\">" counter);
  String.iter (esc_char (ref true)) input_line;
  output_string !current_out_c "</span>";

  (*Print output lines*)
  output_string !current_out_c (Format.asprintf
    "<span class=\"output-line\" id=\"out%d\">" counter);
  let output_line = (Format.flush_str_formatter ()) in
  String.iter (esc_char (ref true)) output_line;
  output_string !current_out_c "</span>";
  
  (*Print commentaries*)
  let print_com s =
    output_string !current_out_c "<span class=\"com-line\">";
    output_string !current_out_c s;
    output_string !current_out_c "</span>"
  in
  List.iter print_com coms

(** *)
let init (filename : string) (html_filename : string) : unit =
  let out_filename = Format.sprintf "%s/%s.html"
    (Filename.dirname html_filename)
    (Filename.(remove_extension @@ basename filename))
  in
  let out_c = open_out out_filename in
  let html_c = open_in html_filename in
  let tag_pos = ref (-1) in
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
    tag_pos := !tag_pos;
    
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

(** *)
let close (filename : string) (html_filename : string) : unit =
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
