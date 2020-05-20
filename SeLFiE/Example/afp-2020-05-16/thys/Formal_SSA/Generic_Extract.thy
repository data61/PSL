(*  Title:      Generic_Extract.thy
    Author:     Sebastian Ullrich, Denis Lohner
*)

theory Generic_Extract imports
  Generic_Interpretation
begin

export_code open
  set sorted_list_of_set disjoint RBT.fold
  gen_ssa_cfg_wf gen_wf_var gen_ssa_wf_notriv_substAll'
  in OCaml module_name BraunSSA

end
