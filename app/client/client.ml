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

(* let libs = ["Prelude.sp"; "Core.sp"; "Logic.sp"; "Set.sp"] *)
(* let base_url = "theories/" *)
  
(* let base_url = (Dom_html.window)##._URL *)

    (*
class type initInfo = object
  method init_pkgs_ : js_string t js_array t readonly_prop
  method all_pkgs_  : js_string t js_array t readonly_prop
  method base_path_ : js_string t            readonly_prop
end
*)
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
  Console.console##log 
    ("cmd in json : " ^ (Yojson.Safe.pretty_to_string ojson));
  SquirrelWorker.jsquirrel_cmd_of_yojson @@ obj_to_json cobj

(* Message from the main thread *)
let on_msg msg =
  let yo = obj_to_json msg in
  Printexc.record_backtrace true;
  (* show json object received for debug info ↓ *)
  Console.console##log ("Got : " ^ (Yojson.Safe.pretty_to_string yo));
  try 
    match jscoq_cmd_of_obj msg with
    | Result.Ok cmd  -> SquirrelWorker.execute_cmd cmd
    | Result.Error s -> Console.console##log  
                          ("Error in JSON conv: " ^ s ^ " | " ^ (Js.to_string (Json.output msg)))
  with e -> Console.console##log  "exec failed";
    Console.console##log ( (Printexc.get_backtrace ()));
        Console.console##log (Printexc.raw_backtrace_to_string (Printexc.get_callstack 12));
         Console.console##log (Printexc.to_string e)

                          

(* let file_cache : (string, string) Hashtbl.t = Hashtbl.create 503 *)

(* let ( let* ) = Lwt.bind *)


(* let http_get url   = *)

(*   (\* Jslog.printf Jslog.jscoq_log "Start preload file %s\n%!" name; *\) *)
(*   let* (resp,body) = Cohttp_lwt_jsoo.Client.get (Uri.of_string url) in *)

(*   let code = resp *)
(*              |> Cohttp.Response.status *)
(*              |> Cohttp.Code.code_of_status in *)
(*   if Cohttp.Code.is_success code *)
(*   then *)
(*     let* b = Cohttp_lwt.Body.to_string body in *)
(*     Lwt.return (Ok b) *)
(*   else *)
(*     Lwt.return (Error ( *)
(*       Cohttp.Code.reason_phrase_of_code code *)
(*     )) *)


  
(* (\* XXX: Wait until we have enough UI support for logging *\) *)
(* let load_file url = *)
(*   Format.eprintf "Loading file %s requested\n%!" url ; *)
(*     let* result = http_get (base_url^url) in *)
(*     match result with *)
(*     | Error str -> *)
(*        Printf.printf "%s:fail\n" url; *)
(*        Printf.printf "Error: %s\n" str; *)
(*        Lwt.return () *)
(*     | Ok result -> *)
(*         Printf.printf "%s:success\n" url; *)
(*         (\* Hashtbl.add file_cache url result; *\) *)
(*         (\* Hashtbl.add file_cache (base_url^url) result; *\) *)
(*         (\* print_string result;          *\) *)
(*         Sys_js.create_file ~name:url ~content:result; *)
(*         Sys_js.create_file ~name:(base_url^url) ~content:result; *)
(*         if url="Prelude.sp" then SquirrelWorker.init () ; *)
(*         (\* print_string result;    *\) *)
(*         Lwt.return () *)


(* let next_tick (_callback : unit -> string) = *)
(*   Js.Unsafe.(fun_call *)
(*                (js_expr "process.nextTick") *)
(*                [| inject (Js.wrap_callback _callback) |]) *)

(* let rec run t = *)
(*   Lwt.wakeup_paused (); *)
(*   match Lwt.poll t with *)
(*     | Some x -> x *)
(*     | None -> next_tick (fun () -> run t) *)

(* let setup_pseudo_fs () = *)
  
(*   Sys_js.unmount ~path:"/static/"; *)
(*   Sys_js.mount ~path:"/static/" (fun ~prefix ~path ->       *)
(*       Format.eprintf "query:%s from %s" path prefix; *)
(*       Hashtbl.find_opt file_cache path *)
(*     ) *)



(* This code is executed on Worker initialization *)
let _ =
  (* This is needed if dynlink is enabled in 4.03.0 *)
  Sys.interactive := false;
  (* setup_pseudo_fs (); *)
  (* List.iter (fun file -> (Lwt.async (fun () -> load_file file))) libs; *)
  (* forward msg when onmessage event occurs *)
  Worker.set_onmessage on_msg

