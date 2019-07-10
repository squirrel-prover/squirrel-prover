open Channel
open Process
open Term
open Constr
open Lexer
open Completion

let parse_theory filename =
  let lexbuf = Lexing.from_channel (Pervasives.open_in filename) in
    try
      Parser.theory Lexer.token lexbuf
    with
      | Parser.Error as e ->
          Format.printf
            "Cannot parse model before %S at position TODO %d.@."
            (Lexing.lexeme lexbuf)
            lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum ;
          raise e
      | e ->
          Format.printf
            "Error before %S at position TODO.@."
            (Lexing.lexeme lexbuf) ;
          raise e

let parse_process string =
  let lexbuf = Lexing.from_string string in
  try
      Parser.top_process Lexer.token lexbuf
  with Parser.Error as e ->
    Format.printf
      "Cannot parse process before %S at position TODO.@."
      (Lexing.lexeme lexbuf) ;
    raise e

let () =
  Checks.add_suite "Parsing" [
    "Null", `Quick, begin fun () ->
      ignore (parse_process "null")
    end ;
    "Simple", `Quick, begin fun () ->
      Channel.reset () ;
      Channel.declare "c" ;
      ignore (parse_process "in(c,x);out(c,x);null") ;
      ignore (parse_process "in(c,x);out(c,x)") ;
      Alcotest.check_raises "fails" Parser.Error
        (fun () -> ignore (parse_process "in(c,x) then null")) ;
      begin match parse_process "(in(c,x);out(c,x) | in(c,x))" with
        | Process.Parallel _ -> ()
        | _ -> assert false
      end ;
      ignore (parse_process "if u then if v then null else null else null") ;
      Channel.reset ()
    end ;
  ]

let () =
  Checks.add_suite "Models" [
    "Null model", `Quick, begin fun () ->
      parse_theory "examples/null.mbc"
    end ;
    "Simple model", `Quick, begin fun () ->
      parse_theory "examples/process.mbc"
    end ;
    (* TODO "LAK model", `Quick, begin fun () ->
      Theory.reset () ;
      Channel.reset () ;
      parse_theory "examples/lak.mbc"
    end ; *)
  ]

let () = Checks.run ()
