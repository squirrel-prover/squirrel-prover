let () =
  Dream.run
  @@ Dream.logger
  @@ Dream.router [

    Dream.get "/"
      (Dream.from_filesystem "_build/default/app/www" "index.html");

    Dream.get "/static/**"
      (Dream.static "_build/default/app/www/static");
  ]
