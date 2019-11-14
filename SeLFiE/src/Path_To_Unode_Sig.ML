(*  Title:      PSL/SeLFeE/src/Full_Path_To_FPUnode_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

This is an improved version of Term_Table.
Term_Table was initially invented for LiFtEr, in which we only needed Full_Path_Table.
In SeLFiEr, however, 

The overall work-flow is:
    (term * Proof.state  ==== trm_to_trm_w_prnt =======================================>                      (* in Unique_Node *)
     trm_w_prnt          ==== trm_w_prnt_to_utrm_w_prnt ===============================>                      (* in Unique_Node *)
     utrm_w_prnt         ==== utrm_w_prnt_to_futrm_w_prnt =============================>                      (* in Unique_Node *)
     futrm_w_prnt        ==== futrm_w_prnt_to_futrm_w_prnt_n_path =====================>                      (* in Unique_Node *)
     futrm_w_prnt_n_path ==== futrm_w_prnt_n_path_to_unodes ===========================>                      (* in Unique_Node *)
     unodes              ==== unodes_to_unode_table ===================================>                      (* in Path_To_Unode  *)
     path_to_unode_table)
*)
structure Path_Table  = Table (type key = UN.path  val ord = path_ord): TABLE;
(*
signature PATH_TO_FPUNODE =
sig

type full_path_to_fpunode_table;

val pst_to_full_path_to_fpunode_table: Proof.state -> full_path_to_fpunode_table;

val fpunode_to_unode:    fpunode -> UN.unode;
val fpunode_to_node :    fpunode -> UN.node;
val fpunode2_to_unode2: (fpunode * fpunode) -> (UN.unode * UN.unode);
val fpunode2_to_node2:  (fpunode * fpunode) -> (UN.node  * UN.node);
*)