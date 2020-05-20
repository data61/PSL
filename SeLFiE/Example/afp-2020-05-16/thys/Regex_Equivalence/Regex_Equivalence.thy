(*  Author: Tobias Nipkow, Dmitriy Traytel *)

section \<open>Various Algorithms for Regular Expression Equivalence\<close>

(*<*)
theory Regex_Equivalence
imports
  Deriv_Autos
  Position_Autos
  After2
  Before2
  "HOL-Library.Code_Target_Nat"
  "Efficient-Mergesort.Efficient_Sort"
begin
(*>*)

export_code
    check_eqv_brz
    check_eqv_brzq
    check_eqv_n
    check_eqv_p
    check_eqv_pn
    check_eqv_b
    check_eqv_b2
    check_eqv_a
    check_eqv_a2
    match_brz
    match_brzq
    match_n
    match_p
    match_pn
    match_b
    match_b2
    match_a
    match_a2
    in SML module_name Rexp

(*<*)
end
(*>*)
