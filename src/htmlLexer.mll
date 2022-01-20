{
  open Lexing
  open HtmlParser
  
  let counter = ref 0
  let buf = Buffer.create 32
}

rule token = parse
| '.'       { Buffer.add_char buf '.';
              let contents = Buffer.contents buf in
              Buffer.reset buf;
              DOT(contents) }
| "(**"     { incr counter;
              comment lexbuf }
| _ as l    { CHAR(l) }

and comment = parse
  | "(*"        { incr counter; 
                  Buffer.add_string buf "(*";
                  comment lexbuf}
  | "*)"        { decr counter;
                  if !counter = 0 then begin
                    let contents = Buffer.contents buf in
                    Buffer.reset buf;
                    COM(contents)
                  end
                  else begin
                    Buffer.add_string buf "*)";
                    comment lexbuf
                  end
                }
| _ as l    { Buffer.add_char buf l;
              comment lexbuf }
