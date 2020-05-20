(*
  Performance check for tree automata stuff
*)

open Ta;;
open Format;;
open Test_setup;;
open Pt_examples;;
open List;;

let reducedTestSet=true;;

let doTest p = match p with 
  (a1,a2) -> Ta.htai_is_empty_witness (Ta.htai_prod a1 a2)
;;

let doTestWR p = match p with 
  (a1,a2) -> Ta.htai_is_empty_witness (Ta.htai_prodWR a1 a2)
;;

let rec prefix l n =
  if n=0 then []
  else if l=[] then []
  else hd l :: prefix (tl l) (n-1)
;;

printf "%s\n" (if reducedTestSet then "[OCaml]!: Using reduced test set" else "Using full test set");;
let tests = if reducedTestSet then prefix Pt_examples.allTests 2 else Pt_examples.allTests;;

let start = Sys.time();;

let res1 = List.map doTest tests;;

let rt = (Sys.time() -. start) *. 1000.0;;

let start = Sys.time();;

let res2 = List.map doTestWR tests;;

let rtWR = (Sys.time() -. start) *. 1000.0;;

printf "[OCaml]! Time: %f ms\n" rt;;
printf "[OCaml]! Time (WR): %f ms\n" rtWR;;
printf "Witnesses:\n %s\n" (Test_setup.concpad "\n" (List.map Test_setup.pretty_witness res1));;
printf "Witnesses (WR):\n %s\n" (Test_setup.concpad "\n" (List.map Test_setup.pretty_witness res2));;
