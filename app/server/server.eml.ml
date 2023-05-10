let home =
  <html>
    <body id="body">
      <p>Hello !</p>
      <script src="/static/client.js"></script>
      <link rel="stylesheet" href="/static/visualisation_style.css">
    </body>
  </html>

let () =
  Dream.run
  @@ Dream.logger
  @@ Dream.router [

    Dream.get "/"
      (fun _ -> Dream.html home);

    Dream.get "/static/**"
      (Dream.static "./static");

  ]
