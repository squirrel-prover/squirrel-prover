(* Squirrel JavaScript API.
 *
 * Part of this code was taken from Jscoq project with ↓
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2021 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2021 Emilio J. Gallego Arias, INRIA
 *
 * Now adapted by ↓
 * Copyright (C) 2022-2023 Thomas Rubiano, CNRS
 * LICENSE: GPLv3+
 *
 * We provide a message-based asynchronous API for communication with
 * Squirrel.
 *)

open Js_of_ocaml
open Jsquirrel
module Html = Dom_html

(* taken from jscoq *)
let rec json_to_obj (cobj : < .. > Js.t) (json : Yojson.Safe.t) : < .. > Js.t =
  let open Js.Unsafe in
  let ofresh j = json_to_obj (obj [||]) j in
  match json with
  | `Bool b   -> coerce @@ Js.bool b
  | `Null     -> pure_js_expr "undefined"
  | `Assoc l  -> List.iter (fun (p, js) -> set cobj p (ofresh js)) l; cobj
  | `List  l  -> Array.(Js.array @@ map ofresh (of_list l))
  | `Float f  -> coerce @@ Js.number_of_float f
  | `String s -> coerce @@ Js.string s
  | `Int m    -> coerce @@ Js.number_of_float (Obj.magic m)
  | `Intlit s -> coerce @@ Js.number_of_float (float_of_string s)
  | `Tuple t  -> Array.(Js.array @@ map ofresh (of_list t))
  | `Variant(_,_) -> pure_js_expr "undefined"

type jsquirrel_answer =
  | Info      of string
  | Goal      of string * string
  | Ok        of int * string * string
  | Ko        of int
  [@@deriving to_yojson]

type jsquirrel_cmd =
  | Undo    of int (* undo n sentences → set current state as
  current-n in the stack *)
  | Exec    of string list (* execute the given sentences and store
  each state in the stack *)
  | NoCheck    of string list (* execute the given sentences and store
  each state in the stack without checking proofs *)
  | Show    of int (* show output of the nth sentence *)
  (* run and ouput a specific command without changing state used for
   print or search for example *)
  | Run     of string 
  | Reset (* will reset prover state *)
  | Info (* will show current state output *)
  [@@deriving yojson]

(* make given message an unsafe json obj *)
let answer_to_jsobj msg =
  let json_msg = jsquirrel_answer_to_yojson msg       in
  json_to_obj (Js.Unsafe.obj [||]) json_msg

(* send string formatted of actual goal with visualisation *)
let show_goal () =
  Common.print_goal (); (* will printout the current goal *)
  let goal_output = Format.flush_str_formatter () in
  Firebug.console##log goal_output;

  let visu : string = Common.visualisation () in
  Worker.post_message (answer_to_jsobj (Goal (goal_output,visu)))

(* send given string to output in goal panel *)
let show_in_goal (goal_output:string) =
  Firebug.console##log goal_output;
  let visu : string = Common.visualisation () in
  Worker.post_message (answer_to_jsobj (Goal (goal_output,visu)))

(* send given string to output in info panel *)
let show_info (info:string) : unit =
  Firebug.console##log info;
  Worker.post_message (answer_to_jsobj (Info info))

(* send OK with number of sentence well executed *)
let send_ok (n:int) : unit =
  let visu : string = Common.visualisation () in
  Common.print_goal (); (* will printout the current goal *)
  let goal_output = Format.flush_str_formatter () in
  Worker.post_message (answer_to_jsobj (Ok (n,goal_output,visu)))

(* send worker that nth sentence fails to execute *)
let send_ko (n:int) : unit =
  Worker.post_message (answer_to_jsobj (Ko (n)))

let rec execute_all' ?(check=`Check) (sentences:string list) (nb:int) (info:string) : string
=
  match sentences with
  | [] -> "No sentences received !" (* should not happend *)
  | [s] -> 
      let ok,info' = Common.exec_sentence ~check s in
      if ok then send_ok nb else send_ko nb;
      (info ^ info')
  | s::t -> 
      let ok,info' = Common.exec_sentence ~check s in
      if ok then 
        (send_ok nb; 
        execute_all' t (nb+1) (info ^ info'))
      else (send_ko nb; (info ^ info'))

(* execute list of sentences and return the concatened infos 
 * Ok or Ko messages can be sent during the process *)
let execute_all ?(check=`Check) (sentences:string list) : string =
  execute_all' ~check sentences 0 ""

let execute_cmd (cmd:jsquirrel_cmd) : unit = 
  match cmd with 
    (* will pop n state from stack and show actual goal *)
    | Undo n -> let _ = Common.popn n in show_goal ()
    (* execute a list of sentences and show concatened infos *)
    | Exec sentences -> 
        let info = execute_all sentences in
        show_info info; show_goal ()
    (* same as Exec but without checking proofs *)
    | NoCheck sentences -> 
        let info = execute_all ~check:`NoCheck sentences in
        show_info info; show_goal ()
    (* show nth state goal DEPRECATED *)
    | Show n -> show_in_goal (Common.shown n)
    (* show actual goal *)
    | Info -> show_in_goal (Common.show ())
    (* Run one given command *)
    | Run s -> show_info (Common.exec_command s)
    (* Reset prover *)
    | Reset -> Common.init (); show_goal ()
