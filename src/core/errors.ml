(** See mli for documentation. *)

type printer =
  (Format.formatter -> Location.t -> unit) ->
  Format.formatter -> unit
type info = {
  printer : printer
}

let handlers : (exn -> info option) list ref = ref []

let register (handler : exn -> info option) : unit =
  handlers := handler :: !handlers

let get_info (e:exn) : info option =
  List.find_map (fun h -> h e) !handlers

let anomaly_info e =
  { printer =
      fun _ fmt ->
        Format.fprintf fmt
          "Anomaly, please report: %s"
          (Printexc.to_string e) }

let pp_user_error pp_loc_error fmt e =
  match get_info e with
  | Some info -> info.printer pp_loc_error fmt
  | _ -> (anomaly_info e).printer pp_loc_error fmt

let is_user_error e = get_info e <> None

let user_mode ~interactive ~test =
  interactive && not test &&
  let params = try Sys.getenv "OCAMLRUNPARAM" with Not_found -> "" in
  not (String.contains params 'b')
