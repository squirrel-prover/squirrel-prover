module S = Tiny_httpd

let update = ref (fun () -> ())

let start () =
  let port = 8080 in
  S._enable_debug false;
  let server = S.create ~port () in

  (* HTML page for showing goals *)

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

  (* Data *)

  S.add_route_handler ~meth:`GET server
    S.Route.(exact "goal" @/ return)
    (fun _req ->
       try
         let goal = Prover.get_first_subgoal () in
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
       update := begin fun () ->
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

let update () = !update ()
