(* Experimental client of JSquirrel *)

open Js_of_ocaml
(* open Js_of_ocaml_lwt *)
open Jsquirrel
module Html = Dom_html

(* tyxml stuff *)

open Js_of_ocaml_tyxml

(* let _action ?(title = "") ?(cl = []) f text = *)
(*   let tit = title in *)
(*   Tyxml_js.Html.( *)
(*     a ~a:[a_title tit; a_class cl; a_onclick (fun _ -> f () ; false)] text) *)

let raw s =
  let open Tyxml_js in
  let div = Dom_html.document##createElement (Js.string "div") in
  div##.innerHTML := Js.string s ;
  Of_dom.of_div div

(* let ( >>= ) = Lwt.bind *)

let replace_child p n =
  Js.Opt.iter p##.firstChild (fun c -> Dom.removeChild p c);
  Dom.appendChild p n

(* let opt_style v default = Js.Optdef.get v (fun () -> default) *)

(* let hello html_content = *)
(*   Eliom_registration.Html_text.create *)
(*     (fun () () -> Lwt.return html_content) *)

let run element view =
  let text = Js.to_string element##.value in
  Firebug.console##log text;
  Common.exec_all text;
  let output = Format.flush_str_formatter () in
  Firebug.console##log output;
  let newpreview = raw output in
  replace_child view (Tyxml_js.To_dom.of_element newpreview)

let onload _ =
  let body = Html.getElementById_exn "body" in
  let d = Html.document in

  let p = Html.(createP document) in
  p##.innerHTML := Js.string ("Coucou petit écureuil !!");
  Firebug.console##log "JSquirrel Loaded !";
  Dom.appendChild body p;

  let textbox = Html.createTextarea d in
  textbox##.rows := 20;
  textbox##.cols := 80;
  textbox##.value := Js.string "channel c
name yo : index->message.
system [S] (A : out(c,diff(zero,empty))).

goal [S] foo (i:index) : happens(A) => output@A = diff(zero,zero).
Proof.
  admit.
Qed.";
  Firebug.console##log (textbox##.value);

  let preview = Html.createDiv d in
  preview##.style##.border := Js.string "1px black dashed";
  preview##.style##.padding := Js.string "5px";

  Dom.appendChild body textbox;
  Dom.appendChild body (Html.createBr d);
  Dom.appendChild body preview;

  let button = Html.createButton d in
  Dom.appendChild button (d##createTextNode (Js.string "Go!"));

  let button_div = Html.createDiv d in
  button_div##.style##.textAlign := Js.string "center";
  button_div##.style##.margin := Js.string "2em auto";
  Dom.appendChild button_div button;
  Dom.appendChild body button_div;
 
  button##.onclick :=
    Html.handler (fun _ ->
        run textbox preview;
        Js._false);

  let _ = Dom.addEventListener textbox Html.Event.keypress
    (Html.handler (fun ev -> 
      let ctrl = Js.to_bool ev##.ctrlKey in
      if not ctrl then Js._true else
      match ev##.keyCode with
      | 13 -> run textbox preview;
          Js._true
      | _ -> Js._true
    )) 
    Js._true in
  
  (* let text = Js.to_string textbox##.value in *)
  (* Common.exec_command text; *)
  (* let output = Format.flush_str_formatter () in *)
  (* let newpreview = raw output in *)
  (* replace_child preview (Tyxml_js.To_dom.of_element newpreview); *)

  (* let rec dyn_preview old_text n = *)
  (*   let text = Js.to_string textbox##.value in *)
  (*   Common.exec_command text; *)
  (*   let output = Format.flush_str_formatter () in *)
  (*   let n = *)
  (*     if text <> old_text *)
  (*     then ( *)
  (*       (try *)
  (*          Firebug.console##log "Dyn preview triggered with :"; *)
  (*          Firebug.console##log text; *)
  (*          Firebug.console##log output *)
  (*          (1* let%html rendered = output in *1) *)
  (*          (1* replace_child preview rendered *1) *)
  (*        with _ -> ()); *)
  (*       20) *)
  (*     else max 0 (n - 1) *)
  (*   in *)
  (*   Lwt_js.sleep (if n = 0 then 0.5 else 0.1) >>= fun () -> dyn_preview text n *)
  (* in *)
  (* ignore (dyn_preview "" 0); *)
  Js._false

let _ = Html.window##.onload := Html.handler onload
