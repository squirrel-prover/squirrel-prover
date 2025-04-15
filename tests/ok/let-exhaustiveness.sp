let bool_to_int (x : bool) with
| true  -> 1
| false -> 0.

let test1 (x : bool * bool) with
| (true , _) -> 1
| (false, _) -> 0.

let test2 (x : bool * bool) with
| (true , _) -> 1
| (false, false) -> 0
| (false, true ) -> 2.
