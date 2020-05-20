(*  
    Title:      Code_Generation_IArrays_Haskell.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Exporting code to Haskell\<close>

theory Code_Generation_IArrays_Haskell
imports    
  Code_Rational
begin

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
  in Haskell
  module_name "Gauss_Haskell" (*file "haskell"*)


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

  bigMatrix
  in Haskell
  module_name "Gauss_Haskell"
  file "haskell"*)

end
