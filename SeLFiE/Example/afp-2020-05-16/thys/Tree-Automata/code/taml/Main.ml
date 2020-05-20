(* To be run within taml-toplevel.
  Unfortunately, we cannot compute a witness for non-emptiness with taml (?)
*)

open Format;;
open List;;

(* Read pair of automata *)
let lt n = (read_automaton ("a1") ("tests/test"^n^".txt"), read_automaton "a2" ("tests/test"^n^".txt"));;

(* Check wether language is empty *)
let test (a1,a2) = is_language_empty (inter a1 a2);;

(* Perform test with id n*)
let testn n = test (lt n);;

let testni n = test (lt (string_of_int n));;

(* Read automata. TODO: Detect available test-files automatically! *)
let pairs = map lt (map string_of_int [0;1]);;

(* Do Checks *)
let start = Sys.time();;
let result = map test pairs;;
let rt = (Sys.time() -. start) *. 1000.0;;

printf "[Taml]! Time: %f ms\n" rt;;
let ress = fold_left (fun s b -> if b then s^" E" else s^" NE") "" result;;
printf "Result: %s\n" ress;;

