(** Main module for the testing binary.
  * See the [Metabc] module for the prover. *)

open Logic

let () = Printexc.record_backtrace true

(** Generic exception for user errors, that should be reported
  * with the given explanation. *)
exception Error of string

(** Given an exception raised during parsing,
  * and a pretty-printer for the location of the error,
  * return [Some pp] where [pp] is a pretty-printer
  * describing the error to the user.
  *
  * For bad, internal errors that should be
  * reported with a backtrace, return [None]. *)
let pp_error pp_loc e = match e with
  | Parser.Error ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[Syntax error %a.@]@."
                pp_loc ())
  | Failure s ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[Error %a: @,%s.@]@."
                pp_loc ()
                s)
  | Theory.Type_error ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[Type error %a.@]@."
                pp_loc ())
  | Theory.Arity_error (s,i,j) ->
      Some (fun ppf () ->
              Fmt.pf ppf
                "@[Arity error %a: @,\
                   %s is passed %d arguments @,\
                   but has arity %d.@]@."
                pp_loc ()
                s i j)
  | _ -> None

(** Pretty-printer for parsing locations. *)
let pp_loc filename lexbuf ppf () =
  Fmt.pf ppf
    "in %s @,\
     at line %d char %d @,\
     before %S"
    filename
    lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum
    (lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum -
     lexbuf.Lexing.lex_curr_p.Lexing.pos_bol)
    (Lexing.lexeme lexbuf)

let parse_from_buf
      ?(test=false) ?(interactive=false) parse_fun lexbuf filename =
  try parse_fun Lexer.token lexbuf with e ->
    let pp_loc = pp_loc filename lexbuf in
      match pp_error pp_loc e with
        | Some pp_error ->
            if test then raise e else
            if interactive then
              let msg = Fmt.strf "%a" pp_error () in
                raise (Error msg)
            else begin
              Fmt.pr "%a" pp_error () ;
              exit 1
            end
        | None ->
            if test || interactive then raise e else begin
              Fmt.pr
                "@[Exception %a: @,%s.@]@.@.\
                 %s@."
                pp_loc ()
                (Printexc.to_string e)
                (Printexc.get_backtrace ()) ;
              exit 1
            end

let parse_theory_buf ?(test=false) lexbuf filename =
  Theory.initialize_symbols () ;
  Process.reset () ;
  parse_from_buf ~test Parser.theory lexbuf filename

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
      ignore (parse_process "if p && p() then out(c,ok)") ;
      ignore (parse_process "if p() = p then out(c,ok)")
    end
  ];;

let () =
  let test = true in
  Checks.add_suite "Models" [
    "Null model", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/null.mbc"
    end ;
    "Simple model", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/process.mbc"
    end ;
    "Name declaration", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/name.mbc"
    end ;
    "Pairs", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/pairs.mbc"
    end ;
    "Basic theory", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/theory.mbc"
    end ;
    "Multiple declarations", `Quick, begin fun () ->
      Alcotest.check_raises "fails"
        (Failure "multiple declarations")
        (fun () -> parse_theory_test ~test "tests/alcotest/multiple.mbc")
    end ;
    "Block creation", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/blocks.mbc" ;
      ignore (Action.find_symbol "IOIO1") ;
      ignore (Action.find_symbol "IOIO2")
      (* TODO test resulting block structure *)
    end ;
    "Let in blocks", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/block_let.mbc"
      (* TODO test resulting block structure *)
    end ;
    "New in blocks", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/block_name.mbc"
      (* TODO test resulting block structure *)
    end ;
    "Find in blocks", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/block_find.mbc"
      (* TODO test resulting block structure *)
    end ;
    "Updates in blocks", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/block_set.mbc"
      (* TODO test resulting block structure *)
    end ;
    "LAK model", `Quick, begin fun () ->
      parse_theory_test ~test "tests/alcotest/lak.mbc"
    end ;
    "LAK model, again", `Quick, begin fun () ->
      (* We do this again, on purpose, to check that all definitions
       * from the previous run are gone. The macros from Term used
       * to not be re-initialized. *)
      parse_theory_test ~test "tests/alcotest/lak.mbc"
    end ;
    (* "Simple goal", `Quick, begin fun () ->
     *   parse_theory_test ~test "tests/alcotest/simple_goal.mbc"
     * end ; *)
  ];;
