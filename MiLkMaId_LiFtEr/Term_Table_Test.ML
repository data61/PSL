(*  Title:      PSL/Term_Table_Test.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
  term                === trm_w_prnt_to_utrm_w_prnt ==================> (* in Unique_Node_Sig.ML *)
  trm_w_prnt          === utrm_w_prnt_to_utrm_w_prnt =================> (* in Unique_Node_Sig.ML *)
  utrm_w_prnt         === utrm_w_prnt_to_utrm_w_prnt =================> (* in Unique_Node_Sig.ML *)
  futrm_w_prnt        === futrm_w_prnt_to_futrm_w_prnt_n_path ========> (* in Unique_Node_Sig.ML *)
  futrm_w_prnt_n_path === futrm_w_prnt_n_path_to_unique_nodes ========> (* in Unique_Node_Sig.ML *)
  unique_nodes        === unique_nodes_to_unique_nodes_w_auxiliary ===> (* in this file *)
  nodes_w_auxiliary
*)

(*&&& and \<Longrightarrow> associate to the right*)
val _ = @{assert} (@{term "A &&& B &&& C"} = @{term "A &&& (B &&& C) "});
val _ = @{assert} (@{term "A \<Longrightarrow> B \<Longrightarrow> C"} = @{term "A \<Longrightarrow> (B \<Longrightarrow> C)"});

(** test utrm_w_prnt_to_utrm_w_prnt **)
local

val xy = @{term "x \<Longrightarrow> y"};

in

end;