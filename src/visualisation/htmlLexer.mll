{
  (* open Lexing *)
  open HtmlParser
  
  let counter = ref 0
  let buf = Buffer.create 32
}

(**)
rule token = parse
| '.'             { DOT }
| "(**"           { incr counter;
                    comment_begin_line lexbuf }
| "(*"            { incr counter;
                    Buffer.add_string buf "(*";
                    simple_comment lexbuf }
| _ as l          { CHAR(l) }

and simple_comment = parse
| "(*"            { incr counter; 
                    Buffer.add_string buf "(*";
                    simple_comment lexbuf}
| "*)"            { decr counter;
                    Buffer.add_string buf "*)";
                    if !counter = 0 then begin
                      let contents = Buffer.contents buf in
                      Buffer.reset buf;
                      STR(contents)
                    end
                    else
                      simple_comment lexbuf }
| _ as l          { Buffer.add_char buf l;
                    simple_comment lexbuf }

and comment = parse
| "(*"            { incr counter; 
                    Buffer.add_string buf "(*";
                    comment lexbuf}
| "*)"            { decr counter;
                    if !counter = 0 then begin
                      let contents = Buffer.contents buf in
                      Buffer.reset buf;
                      COM(contents)
                    end
                    else begin
                      Buffer.add_string buf "*)";
                      comment lexbuf
                    end }
| '\n'            { Buffer.add_char buf '\n';
                    comment_begin_line lexbuf }
| _ as l          { Buffer.add_char buf l;
                    comment lexbuf }

and comment_begin_line = parse
| "(*"            { incr counter; 
                    Buffer.add_string buf "(*";
                    comment lexbuf}
| "*)"            { decr counter;
                    if !counter = 0 then begin
                      let contents = Buffer.contents buf in
                      Buffer.reset buf;
                      COM(contents)
                    end
                    else begin
                      Buffer.add_string buf "*)";
                      comment lexbuf
                    end }
| [' ' '\r' '\t'] { comment_begin_line lexbuf }
| '\n'            { Buffer.add_char buf '\n';
                    comment_begin_line lexbuf }
| _ as l          { Buffer.add_char buf l;
                    comment lexbuf }
