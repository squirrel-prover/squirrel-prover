let current_out_c = ref stdout

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

(** Printing of html output *)
let pp in_chan p1 p2 counter =
  (*Print input lines*)
  let input_line = really_input_string in_chan (p2-p1) in
  output_string !current_out_c (Format.asprintf 
    "<span class=\"input-line\" id=\"in%d\">" counter);
  String.iter (esc_char (ref true)) input_line;
  output_string !current_out_c "</span>";

  (*Print output lines*)
  output_string !current_out_c (Format.asprintf
    "<span class=\"output-line\" id=\"out%d\">" counter);
  let output_line = (Format.flush_str_formatter ()) in
  String.iter (esc_char (ref true)) output_line;
  output_string !current_out_c "</span>"

(** *)
let create_out_channel (filename : string) (html_filename : string) : out_channel * int =
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
    (out_c, !tag_pos)
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
let close (out_c : out_channel) (html_filename : string) (pos : int) : unit =
  output_string out_c "</span>";
  let html_c = open_in html_filename in
  seek_in html_c pos;
  try
    while true do
      let line = input_line html_c in
      output_string out_c (line ^ "\n")
    done;
  with
    | End_of_file ->
      close_in html_c;
      close_out out_c;
      current_out_c := stdout
