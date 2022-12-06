module S = Tiny_httpd

(* Utilities for reading files from script/ directory,
   whose location is determined from the binary's path. *)

let read_whole_file filename =
  let ch = open_in filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s

let make_absolute path =
  if Filename.is_relative path then
    Filename.concat Filename.current_dir_name path
  else
    path

let repository = Filename.dirname (make_absolute Sys.argv.(0))

let read_file filename =
  read_whole_file
    (Filename.concat repository (Filename.concat "scripts/visualisation" filename))

(* Function to send update events. It will be updated when creating
   the corresponding route in the server. *)

let update : (Prover.state -> unit) ref = ref (fun (_) -> ())

let prover_state : Prover.state ref = ref (Prover.init ())

(* Server setup and launching in a new thread *)

let start () =
  if Sys.getenv_opt("SP_VISU") = Some("ok") then
  begin
    let port = 8080 in
    S._enable_debug false;
    let server = S.create ~port () in

    (* Hardcoded HTML pages *)

    let goals_page = "\
<html>
  <head><script>
     const es = new EventSource(\"events\");
     var nbupdates = 0;
     es.addEventListener(\"update\",
       function(event){
         nbupdates++;
         document.getElementById(\"nbupdates\").innerHTML=nbupdates;
         fetch(\"goal\")
           .then(response => response.text())
           .then(data => document.getElementById(\"goal\").innerHTML = data);
       });
  </script></head>
  <body>
    <p>Update events so far: <span id=\"nbupdates\">0</span>.</p>
    <p>Current goal:</p>
    <div id=\"goal\" style=\"white-space:pre;font-family:monospace\">\
       none</verbatim>
  <body>
</html>"
  in

    S.add_route_handler ~meth:`GET server
      S.Route.(exact "goals" @/ return)
      (fun _req -> S.Response.make_string (Ok goals_page));

    let default_page =
      "<html><body><p>\
        Try <a href=\"goals\">this</a> \
        or <a href=\"visualisation.html\">that</a>.\
       </p></body></html>"
    in
    S.add_route_handler ~meth:`GET server
      S.Route.return
      (fun _req -> S.Response.make_string (Ok default_page));

    (* Serving files from scripts directory *)

    List.iter
      (fun filename ->
         S.add_route_handler ~meth:`GET server
           S.Route.(exact filename @/ return)
           (fun _req -> S.Response.make_string (Ok (read_file filename)))) ["visualisation.html";"visualisation_style.css";"visualisation_script.js";"favicon.ico"];

    (* Data *)
  
    let headers = [("Content-Type", "text/plain")] in
    S.add_route_handler ~meth:`GET server
      S.Route.(exact "dump.json" @/ return)
      (fun _req ->
         match Prover.get_first_subgoal !prover_state with
           | Trace j ->
               let json =
                 Format.asprintf "%a"
                   Visualisation.pp j
               in
               S.Response.make_string ~headers:headers (Ok json)
           | _ | exception _ -> 
               let json = "{\"error\": \"Nothing to visualise\"}" in
               S.Response.make_string ~headers:headers (Ok json));

    S.add_route_handler ~meth:`GET server
      S.Route.(exact "goal" @/ return)
      (fun _req ->
         try
           let goal = Prover.get_first_subgoal !prover_state in
           S.Response.make_string (Ok (Format.asprintf "%a" Goal.pp goal))
         with _ ->
           S.Response.make_string (Ok "none"));

    (* Events *)

    let extra_headers = [
      "Access-Control-Allow-Origin", "*";
      "Access-Control-Allow-Methods", "POST, GET, OPTIONS";
    ] in
    S.add_route_server_sent_handler server S.Route.(exact "events" @/ return)
      (fun _req (module EV : S.SERVER_SENT_GENERATOR) ->
         S._debug (fun k -> k "new connection");
         EV.set_headers extra_headers;
         update := begin fun (ps:Prover.state) ->
           prover_state := ps;
           S._debug (fun k -> k "update event %.2f" (Unix.gettimeofday ()));
           EV.send_event ~event:"update" ~data:"" ();
         end;
         while true do Unix.sleepf 60. done);

    let run () =
      Printf.printf "Listening on http://localhost:%d/\n%!" (S.port server);
      match S.run server with
        | Ok () -> ()
        | Error e ->
            Printf.eprintf "error: %s\n%!" (Printexc.to_string e); exit 1
    in
    ignore (Thread.create run ())
  end

let update (ps:Prover.state) : unit = !update (ps)
