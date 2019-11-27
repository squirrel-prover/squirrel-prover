
exception Tactic_Hard_Failure of string

type tac_error =
  | Failure of string
  | AndThen_Failure of tac_error

let rec pp_tac_error ppf = function
  | Failure s -> Fmt.pf ppf "%s" s
  | AndThen_Failure t ->
      Fmt.pf ppf
        "An application of the second tactic to one \
         of the subgoal failed with error : %a"
        pp_tac_error t

type 'a fk = tac_error -> 'a

type ('a,'b) sk = 'a -> 'b fk -> 'b

type ('a,'j) tac = 'j -> ('j list,'a) sk -> 'a fk -> 'a

(** Basic Tactics *)

let fail sk fk = fk (Failure "fail")

let wrap f v sk fk = sk (f v) fk

let return a v = a v (fun r fk' -> r) (fun _ -> raise @@ Failure "return")

(** [map t [e1;..;eN]] returns all possible lists [l1@..@lN]
  * where [li] is a result of [t e1]. *)
let map t l sk fk =
  let rec aux acc l sk fk = match l with
    | [] -> sk (List.rev acc) fk
    | e::l ->
        t e
          (fun r fk ->
             aux (List.rev_append r acc) l sk fk)
          fk
  in aux [] l sk fk

let orelse_nojudgment a b sk fk = a sk (fun tac_error -> b sk fk)

let orelse a b j sk fk = orelse_nojudgment (a j) (b j) sk fk

let orelse_list l j =
  List.fold_right (fun t t' -> orelse_nojudgment (t j) t') l fail

let andthen tac1 tac2 judge sk fk =
  tac1 judge
    (fun l fk -> map tac2 l sk fk)
    fk

let rec andthen_list = function
  | [] -> raise (Tactic_Hard_Failure "empty anthen_list")
  | [t] -> t
  | t::l -> andthen t (andthen_list l)

let repeat t j sk fk =
  let rec aux j sk fk =
    t j
      (fun l fk -> map aux l sk fk)
      (fun e -> sk [j] fk)
  in aux j sk fk
