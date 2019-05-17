(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_list_count_nub
  imports "../../Test_Base" "../../../MeLoId_LiFtEr"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

fun filter :: "('a => bool) => 'a list => 'a list" where
  "filter p (nil2) = nil2"
| "filter p (cons2 y xs) =
     (if p y then cons2 y (filter p xs) else filter p xs)"

(*fun did not finish the proof*)
function nubBy :: "('a => ('a => bool)) => 'a list => 'a list" where
  "nubBy x (nil2) = nil2"
| "nubBy x (cons2 z xs) =
     cons2 z (nubBy x (filter (% (y2 :: 'a) => (~ ((x z) y2))) xs))"
by pat_completeness auto

fun elem :: "'a => 'a list => bool" where
  "elem x (nil2) = False"
| "elem x (cons2 z xs) = ((z = x) | (elem x xs))"

fun count :: "'a => 'a list => int" where
  "count x (nil2) = 0"
| "count x (cons2 z ys) =
     (if (x = z) then 1 + (count x ys) else count x ys)"

theorem property0 :
  "((elem x xs) ==>
      ((count x (nubBy (% (y :: 'a) => % (z :: 'a) => (y = z)) xs)) =
         1))"
  oops

ML{* open Pattern;*}

ML{*
mk_pattern_matrix                       @{context} "nubBy";
ctxt_n_name_to_patterns_of_each_param   @{context} "nubBy";

val _ = @{assert} (is_nth_all_Only_Var                     @{context} "nubBy" 0       );
val _ = @{assert} (is_nth_all_Only_Var                     @{context} "nubBy" 1 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_W_Var       @{context} "nubBy" 0 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_W_Var       @{context} "nubBy" 1 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_WO_Var      @{context} "nubBy" 0 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_WO_Var      @{context} "nubBy" 1 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_W_or_WO_Var @{context} "nubBy" 0 |> not);
val _ = @{assert} (is_nth_all_Data_Constructor_W_or_WO_Var @{context} "nubBy" 1       );
*}

end
