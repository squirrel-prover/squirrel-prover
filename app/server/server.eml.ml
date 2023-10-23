(* A Dream server to easily serve the client
 *
 * TODO :
 * - a start for client-server squirrel on browser
 *)

let () =
  Dream.run
  @@ Dream.logger
  @@ Dream.router [

    Dream.get "/"
      (Dream.from_filesystem "_build/default/app/www" "index.html");

    Dream.get "/static/**"
      (Dream.static "_build/default/app/www/static");

    Dream.get "/documentation/**"
      (Dream.static "_build/default/documentation/sphinx/public");
  ]
