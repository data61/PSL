section \<open>All ICF Implementations\<close>
theory ICF_Impl
imports
  (*"../../Refine_Monadic/Refine_Monadic"*)
(* Interfaces *)
  "spec/SetSpec"
  "spec/MapSpec"
  "spec/ListSpec"
  "spec/AnnotatedListSpec"
  "spec/PrioSpec"
  "spec/PrioUniqueSpec"
(* Generic Algorithms *)
  "gen_algo/Algos"
  "gen_algo/SetIndex"
(* Implementations *)
  "impl/SetStdImpl"
  "impl/MapStdImpl"
  "impl/Fifo"
  "impl/BinoPrioImpl"
  "impl/SkewPrioImpl"
  "impl/FTAnnotatedListImpl"
  "impl/FTPrioImpl"
  "impl/FTPrioUniqueImpl"
begin


end
