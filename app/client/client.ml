(* Experimental worker of JSquirrel
 * Inspired by JsCoq ↓
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2021 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2021 Emilio J. Gallego Arias, INRIA
 *
 * Adapted for JSquirrel by ↓
 * Copyright (C) 2022-2023 Thomas Rubiano, CNRS
 * LICENSE: GPLv3+
 *
 * We provide a message-based asynchronous API for communication with
 * Squirrel.
 *)

open Js_of_ocaml

module Html = Dom_html

(* taken fron jscoq but mainly list of string will be used here *)
let rec obj_to_json (cobj : < .. > Js.t) : Yojson.Safe.t =
  let open Js in
  let open Js.Unsafe in
  let typeof_cobj = to_string (typeof cobj) in
  match typeof_cobj with
  | "string"  -> `String (to_string @@ coerce cobj)
  | "boolean" -> `Bool (to_bool @@ coerce cobj)
  | "number"  -> `Int (int_of_float @@ float_of_number @@ coerce cobj)
  | _ ->
      if instanceof cobj array_empty then
        `List Array.(to_list @@ map obj_to_json @@ to_array @@ coerce cobj)
      else if instanceof cobj Typed_array.arrayBuffer then
        `String (Typed_array.String.of_arrayBuffer @@ coerce cobj)
      else if instanceof cobj Typed_array.uint8Array then
        `String (Typed_array.String.of_uint8Array @@ coerce cobj)
      else
        let json_string = Js.to_string (Json.output cobj) in
        Yojson.Safe.from_string json_string

let jscoq_cmd_of_obj (cobj : < .. > Js.t) =
  let ojson = obj_to_json cobj in
  (* will show in console the json object for debug info ↓ *)
  Firebug.console##log 
    ("cmd in json : " ^ (Yojson.Safe.pretty_to_string ojson));
  SquirrelWorker.jsquirrel_cmd_of_yojson @@ obj_to_json cobj

(* Message from the main thread *)
let on_msg msg =
  let yo = obj_to_json msg in
  (* show json object received for debug info ↓ *)
  Firebug.console##log ("Got : " ^ (Yojson.Safe.pretty_to_string yo));

  match jscoq_cmd_of_obj msg with
  | Result.Ok cmd  -> SquirrelWorker.execute_cmd cmd
  | Result.Error s -> Firebug.console##log  
        ("Error in JSON conv: " ^ s ^ " | " ^ (Js.to_string (Json.output msg)))

(* This code is executed on Worker initialization *)
let _ =
  (* This is needed if dynlink is enabled in 4.03.0 *)
  Sys.interactive := false;
  (* forward msg when onmessage event occurs *)
  Worker.set_onmessage on_msg

