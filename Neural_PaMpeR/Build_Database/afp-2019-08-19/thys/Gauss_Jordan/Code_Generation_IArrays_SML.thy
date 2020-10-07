(*  
    Title:      Code_Generation_IArrays_SML.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Exporting code to SML\<close>

theory Code_Generation_IArrays_SML
imports
  "HOL-Library.Code_Real_Approx_By_Float"
  Code_Generation_IArrays
begin

text\<open>Some serializations of gcd and abs in SML. Since gcd is not part of the standard SML library,
we have serialized it to the corresponding operation in PolyML and MLton.\<close>

context
includes integer.lifting
begin

lift_definition gcd_integer :: "integer => integer => integer"
  is "gcd :: int => int => int" .


lemma gcd_integer_code[code]:
"gcd_integer l k = \<bar>if l = (0::integer) then k else gcd_integer l (\<bar>k\<bar> mod \<bar>l\<bar>)\<bar>"
apply (transfer) using gcd_code_int by (metis gcd.commute)
end

code_printing
 constant "abs :: integer => _" \<rightharpoonup> (SML) "IntInf.abs"
 | constant "gcd_integer :: integer => _ => _" \<rightharpoonup> (SML) "(PolyML.IntInf.gcd ((_),(_)))" (*Only for Poly/ML*)
 (* | constant "gcd_integer :: integer => _ => _" \<rightharpoonup> (SML) "(MLton.IntInf.gcd ((_),(_)))"*) (*Only for MLton*)

lemma gcd_code[code]:
"gcd a b = int_of_integer (gcd_integer (of_int a) (of_int b))"
by (metis gcd_integer.abs_eq int_of_integer_integer_of_int integer_of_int_eq_of_int)

code_printing
  constant "abs :: real => real" \<rightharpoonup>
    (SML) "Real.abs"

declare [[code drop: "abs :: real \<Rightarrow> real"]]
  
text\<open>There are several ways to serialize div and mod. The following ones are four examples of it:\<close>

(*The times are obtained after computing the rref of a 100x100 rational matrix.*)

(* 21.484 seconds*)
(*
code_printing
constant "divmod_integer :: integer => _ => _" \<rightharpoonup> (SML) "(IntInf.divMod ((_),(_)))"
*)

(*19.04 seconds*)
(*
code_printing
constant "(div) :: integer => _ => _" \<rightharpoonup> (SML) "(IntInf.div ((_), (_)))"
| constant "(mod) :: integer => _ => _" \<rightharpoonup> (SML) "(IntInf.mod ((_), (_)))"
*)

(*18.832 seconds*)
(*
code_printing
constant "(div) :: integer => _ => _" \<rightharpoonup> (SML) "(IntInf.quot ((_), (_)))"
| constant "(mod) :: integer => _ => _" \<rightharpoonup> (SML) "(IntInf.rem ((_), (_)))"
*)

(*18.792 seconds*)
(*
code_printing
constant "divmod_integer :: integer => _ => _" \<rightharpoonup> (SML) "(IntInf.quotRem ((_),(_)))"
*)

(*Thus, the best option for our development is:*)

code_printing
constant "divmod_integer :: integer => _ => _" \<rightharpoonup> (SML) "(IntInf.quotRem ((_),(_)))"

export_code
  print_rank_real
  print_rank_rat
  print_rank_z2
  print_rank
  print_result_real
  print_result_rat
  print_result_z2
  print_result_Gauss
  print_det_rat
  print_det_real
  print_det
  print_inverse_real
  print_inverse_rat
  print_inverse
  print_system_rat
  print_system
  in SML module_name "Gauss_SML" (*file "Gauss_SML.sml"*)
  
(* For the Mathematica bug:*)

(*
export_code
  print_rank_real
  print_rank_rat
  print_rank_z2
  print_rank
  print_result_real
  print_result_rat
  print_result_z2
  print_result_Gauss
  print_det_rat 
  print_det_real
  print_det
  print_inverse_real
  print_inverse_rat
  print_inverse
  print_system_rat
  print_system

  bigMatrix
  in SML module_name "Gauss_SML" file "Gauss_SML.sml"
*)

end
