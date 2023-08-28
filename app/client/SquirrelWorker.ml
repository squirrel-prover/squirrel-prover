open Js_of_ocaml
(* open Js_of_ocaml_lwt *)
open Jsquirrel
module Html = Dom_html

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
  | Ok        of int * string
  | Ko        of int * string
  [@@deriving to_yojson]

(* let cast = Js_of_ocaml_tyxml.Tyxml_js.To_dom.of_element *)

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

let answer_to_jsobj msg =
  let json_msg = jsquirrel_answer_to_yojson msg       in
  json_to_obj (Js.Unsafe.obj [||]) json_msg

(* let output_node () = *) 
(*       Firebug.console##warn "query-panel not found ?" *)
let output_node () = 
  match Html.getElementById_opt "query-panel" with
  | Some e -> e
  | None -> 
      Firebug.console##warn "query-panel not found ?";
      Html.getElementById "query-panel"

let goal_node () = 
      Firebug.console##warn "goal-text not found ?"
(* let goal_node () = *) 
(*   match Html.getElementById_opt "goal-text" with *)
(*   | Some e -> e *)
(*   | None -> *) 
(*       Firebug.console##warn "goal-text not found ?"; *)
(*       Html.getElementById "goal-text" *)

let show_goal () =
  Common.print_goal (); (* will printout the current goal *)
  let goal_output = Format.flush_str_formatter () in
  Firebug.console##log goal_output;

  let visu : string = Common.visualisation () in
  Worker.post_message (answer_to_jsobj (Goal (goal_output,visu)))
  (* let newgoal = H.raw goal_output in () *)
  (* H.replace_child (goal_node ()) (H.cast newgoal) *)

let show_in_goal (goal_output:string) =
  Firebug.console##log goal_output;
  let visu : string = Common.visualisation () in
  Worker.post_message (answer_to_jsobj (Goal (goal_output,visu)))
  (* let newgoal = H.raw goal_output in *)
  (* H.replace_child (goal_node ()) (H.cast newgoal) *)

let show_info (info:string) : unit =
  Firebug.console##log info;
  Worker.post_message (answer_to_jsobj (Info info))

  (* let newpreview = raw info in *)
  (* replace_child (output_node ()) (cast newpreview) *)

(* send OK with number of sentence well executed *)
let send_ok (n:int) : unit =
  let visu : string = Common.visualisation () in
  Worker.post_message (answer_to_jsobj (Ok (n,visu)))

let send_ko (n:int) : unit =
  let visu : string = Common.visualisation () in
  Worker.post_message (answer_to_jsobj (Ko (n,visu)))

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

(* return the concatened infos *)
let execute_all ?(check=`Check) (sentences:string list) : string =
  execute_all' ~check sentences 0 ""

let execute_cmd (cmd:jsquirrel_cmd) : unit = 
  match cmd with 
    | Undo n -> let _ = Common.popn n in show_goal ()
    | Exec sentences -> 
        let info = execute_all sentences in
        show_info info; show_goal ()
    | NoCheck sentences -> 
        let info = execute_all ~check:`NoCheck sentences in
        show_info info; show_goal ()
    | Show n -> show_in_goal (Common.shown n)
    | Info -> show_in_goal (Common.show ())
    | Run s -> show_info (Common.exec_command s)
    | Reset -> Common.init (); show_goal ()
