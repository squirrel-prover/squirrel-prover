(** Main module for the testing binary.
  * See the [Metabc] module for the prover. *)

open Logic

let () = Printexc.record_backtrace true


let parse_from_buf ?(test=false) ?(interactive=false) parse_fun lexbuf filename =
  try parse_fun Lexer.token lexbuf with
  | Parser.Error as e ->
    if not(interactive) then
      (
    Printexc.print_backtrace Pervasives.stderr;
    Format.printf
      "@[Error in %S @,at line %d char %d @,\
       before %S.@]@."
      filename
      lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
      (lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum -
       lexbuf.Lexing.lex_curr_p.Lexing.pos_bol)
      (Lexing.lexeme lexbuf) );
    if test || interactive then raise e else exit 1
  | Failure s as e ->
    if not(interactive) then
      (    
    Format.printf
      "@[Error in %S @,at line %d char %d @,\
       before %S: @,%s.@]@."
      filename
      lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
      (lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum -
       lexbuf.Lexing.lex_curr_p.Lexing.pos_bol)
      (Lexing.lexeme lexbuf)
      s );
    if test || interactive then raise e else exit 1
  | e ->
    if not(interactive) then
      (
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
      (Printexc.to_string e)) ;
    if test || interactive then raise e else exit 1

let parse_theory_buf ?(test=false) lexbuf filename =
  Theory.initialize_symbols () ;
  Process.reset () ;
  parse_from_buf ~test:test Parser.theory lexbuf filename

let parse_goal_buf ?(test=false) lexbuf filename =
  parse_from_buf ~test:test Parser.goal lexbuf filename

let parse_interactive_buf ?(test=false) lexbuf filename =
  parse_from_buf ~test:test ~interactive:true Parser.interactive lexbuf filename


let parse_tactic_buf ?(test=false) lexbuf filename =
  parse_from_buf ~test:test Parser.tactic lexbuf filename

let parse_qed_buf ?(test=false) lexbuf filename =
  parse_from_buf ~test:test Parser.qed lexbuf filename

let parse_undo_buf ?(test=false) lexbuf filename =
  parse_from_buf ~test:test Parser.undo lexbuf filename


let parse_process string =
  let lexbuf = Lexing.from_string string in
  try
    Parser.top_process Lexer.token lexbuf
  with Parser.Error as e ->
    Format.printf
      "Cannot parse process before %S at position TODO.@."
      (Lexing.lexeme lexbuf) ;
    raise e

let parse_theory_test ?(test=false) filename =
    let lexbuf = Lexing.from_channel (Pervasives.open_in filename) in
    parse_theory_buf ~test lexbuf filename

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
      parse_theory_test ~test "examples/null.mbc"
    end ;
    "Simple model", `Quick, begin fun () ->
      parse_theory_test ~test "examples/process.mbc"
    end ;
    "Name declaration", `Quick, begin fun () ->
      parse_theory_test ~test "examples/name.mbc"
    end ;
    "Pairs", `Quick, begin fun () ->
      parse_theory_test ~test "examples/pairs.mbc"
    end ;
    "Basic theory", `Quick, begin fun () ->
      parse_theory_test ~test "examples/theory.mbc"
    end ;
    "Multiple declarations", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "multiple declarations")
        (fun () -> parse_theory_test ~test "examples/multiple.mbc")
    end ;
    "Block creation", `Quick, begin fun () ->
      parse_theory_test ~test "examples/blocks.mbc"
      (* TODO test resulting block structure *)
    end ;
    "Let in blocks", `Quick, begin fun () ->
      parse_theory_test ~test "examples/block_let.mbc"
      (* TODO test resulting block structure *)
    end ;
    "New in blocks", `Quick, begin fun () ->
      parse_theory_test ~test "examples/block_name.mbc"
      (* TODO test resulting block structure *)
    end ;
    "Find in blocks", `Quick, begin fun () ->
      parse_theory_test ~test "examples/block_find.mbc"
      (* TODO test resulting block structure *)
    end ;
    "Updates in blocks", `Quick, begin fun () ->
      parse_theory_test ~test "examples/block_set.mbc"
      (* TODO test resulting block structure *)
    end ;
    "LAK model", `Quick, begin fun () ->
      parse_theory_test ~test "examples/lak.mbc"
    end ;
    (* "Simple goal", `Quick, begin fun () ->
     *   parse_theory_test ~test "examples/simple_goal.mbc"
     * end ; *)
  ];;

let pp_descrs ppf () =
  Fmt.pf ppf "@[<v 2>Available actions:@;@;";
  Process.iter_csa (fun descr ->
      Fmt.pf ppf "@[<v 0>@[%a@]@;@]@;"
        Process.pp_descr descr) ;
  Fmt.pf ppf "@]%!@."

let pp_proc ppf () =
  Process.show_actions ppf () ;
  Fmt.pf ppf "@." ;
  pp_descrs ppf ()

let pp_goals ppf () =
  let cpt = ref 0 in
  Fmt.pf ppf "@[<v>";
  Logic.iter_goals (fun (gname,goal) ->
      Fmt.pf ppf "@[<v>%d: @[@[%a@]@;@]@]@;"
        !cpt Term.pp_formula goal;
      incr cpt;);
  Fmt.pf ppf "@]%!@.";;
