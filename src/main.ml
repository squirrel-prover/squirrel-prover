open Logic

let () = Printexc.record_backtrace true

let parse_theory ?(test=false) filename =
  Theory.initialize_symbols () ;
  Process.reset () ;
  let lexbuf = Lexing.from_channel (Pervasives.open_in filename) in
    try
      Parser.theory Lexer.token lexbuf
    with
    | Parser.Error as e ->
      Printexc.print_backtrace Pervasives.stderr;
      Format.printf
        "@[Cannot parse model @,\
         in %S @,at line %d char %d @,\
         before %S.@]@."
        filename
        lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
        (lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum -
         lexbuf.Lexing.lex_curr_p.Lexing.pos_bol)
        (Lexing.lexeme lexbuf) ;
      if test then raise e else exit 1
    | Failure s as e ->
      Format.printf
        "@[Error in %S @,at line %d char %d @,\
         before %S: @,%s.@]@."
        filename
        lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
        (lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum -
         lexbuf.Lexing.lex_curr_p.Lexing.pos_bol)
        (Lexing.lexeme lexbuf)
        s ;
      if test then raise e else exit 1
    | e ->
      Printexc.print_backtrace Pervasives.stderr;
      Format.printf
        "@[Error @,\
         in %S @,at line %d char %d @,\
         before %S: @,%s.@]@."
        filename
        lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
        (lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum -
         lexbuf.Lexing.lex_curr_p.Lexing.pos_bol)
        (Lexing.lexeme lexbuf)
        (Printexc.to_string e) ;
      if test then raise e else exit 1

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
    "Pairs", `Quick, begin fun () ->
      Theory.initialize_symbols () ;
      Channel.declare "c" ;
      ignore (parse_process "in(c,x);out(c,<x,x>)")
    end ;
    "Facts", `Quick, begin fun () ->
      Theory.initialize_symbols () ;
      Theory.declare_abstract "p" [] Theory.Boolean ;
      Channel.declare "c" ;
      ignore (parse_process "if p and p() then out(c,ok)") ;
      ignore (parse_process "if p() = p then out(c,ok)")
    end
  ];;

let () =
  let test = true in
  Checks.add_suite "Models" [
    "Null model", `Quick, begin fun () ->
      parse_theory ~test "examples/null.mbc"
    end ;
    "Simple model", `Quick, begin fun () ->
      parse_theory ~test "examples/process.mbc"
    end ;
    "Name declaration", `Quick, begin fun () ->
      parse_theory ~test "examples/name.mbc"
    end ;
    "Pairs", `Quick, begin fun () ->
      parse_theory ~test "examples/pairs.mbc"
    end ;
    "Basic theory", `Quick, begin fun () ->
      parse_theory ~test "examples/theory.mbc"
    end ;
    "Multiple declarations", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "multiple declarations")
        (fun () -> parse_theory ~test "examples/multiple.mbc")
    end ;
    "LAK model", `Quick, begin fun () ->
      parse_theory ~test "examples/lak.mbc"
    end ;
  ];;


let pp_proc ppf =
  let cpt = ref 0 in
  Fmt.pf ppf "@[<v>";
  Process.iter_csa (fun descr ->
      Fmt.pf ppf "%d:@;@[%a@]@;done@;"
        !cpt Process.pp_descr descr);
  incr cpt;
  Fmt.pf ppf "@]%!@.";;
