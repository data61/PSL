(*<*)
theory Monitor_Code
  imports Monitor_Impl
begin
(*>*)

export_code convert_multiway minit_safe mstep mmonitorable_exec
   checking OCaml?

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  String.explode String.implode interval mk_db
  RBT_set rbt_empty rbt_insert rbt_fold
  (*term, formula, and regex constructors*)
  EInt Formula.Var Formula.Agg_Cnt Formula.Pred Regex.Skip Regex.Wild
  (*main functions*)
  convert_multiway minit_safe mstep mmonitorable_exec
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)