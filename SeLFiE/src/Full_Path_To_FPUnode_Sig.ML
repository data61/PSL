(*  Title:      PSL/SeLFeE/src/Full_Path_To_FPUnode_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The overall work-flow is:
 Proof.state           ==== pst_to_location_n_term_list =========================================>            (* in Full_Path_To_Unode_Struct *)
 Proof.state * (location * term) list ==== pst_n_location_n_term_list_to_location_n_path_to_unode_table ====> (* in Full_Path_To_Unode_Struct *)
    (term * Proof.state  ==== trm_to_trm_w_prnt =======================================>                      (* in Unique_Node *)
     trm_w_prnt          ==== trm_w_prnt_to_utrm_w_prnt ===============================>                      (* in Unique_Node *)
     utrm_w_prnt         ==== utrm_w_prnt_to_futrm_w_prnt =============================>                      (* in Unique_Node *)
     futrm_w_prnt        ==== futrm_w_prnt_to_futrm_w_prnt_n_path =====================>                      (* in Unique_Node *)
     futrm_w_prnt_n_path ==== futrm_w_prnt_n_path_to_unodes ===========================>                      (* in Unique_Node *)
     unodes              ==== unodes_to_unode_table ===================================>                      (* in Term_Table  *)
     path_to_unode_table)
(location * path_to_unode_table) list ==== location_n_path_to_unode_table_list_to_location_n_full_path_to_fpunode_table_list =====> (* in Full_Path_To_Unode_Struct *)
    ((location * path_to_unode_table) ==== location_n_path_to_unode_table_to_full_path_to_fpunode_table ==========================> (* in Full_Path_To_Unode_Struct *)
      full_path_to_fpunode_table)
(location * full_path_to_fpunode_table) list ==== map snd =======================================================================> (* in Full_Path_To_Unode_Struct *)
 full_path_to_fpunode_table) list            ==== merge_full_path_to_fpunode_tables =============================================> (* in Full_Path_To_Unode_Struct *)
 full_path_to_fpunode_table
*)
datatype location = Subgoal of int | Chained_Fact of int;

fun are_same_location (Subgoal      n) (Subgoal      m) = n = m
  | are_same_location (Chained_Fact n) (Chained_Fact m) = n = m
  | are_same_location  _                _               = false;

type full_path = location * UN.path;

(*This definition is more or less arbitrary.*)
fun full_path_ord ((Subgoal n, path1), (Subgoal m, path2)) =
    (case Int.compare (n, m) of EQUAL => path_ord (path1, path2) | diff  => diff)
  | full_path_ord ((Chained_Fact n, path1), (Chained_Fact m, path2)) =
    (case Int.compare (n, m) of EQUAL => path_ord (path1, path2) | diff  => diff)
  | full_path_ord ((Subgoal      _, _), (Chained_Fact _, _)) = GREATER
  | full_path_ord ((Chained_Fact _, _), (Subgoal      _, _)) = LESS

fun full_path_eq (full_p1:full_path, full_p2:full_path) = case full_path_ord (full_p1, full_p2) of
  EQUAL => true | _ => false;

structure Full_Path_Table  = Table (type key = full_path  val ord = full_path_ord): TABLE;

signature FULL_PATH_TO_FPUNODE =
sig

type fpunode =
  {unode     : UN.unode,
   location  : location};

type full_path_to_fpunode_table;

val pst_to_full_path_to_fpunode_table: Proof.state -> full_path_to_fpunode_table;

val fpunode_to_unode:    fpunode -> UN.unode;
val fpunode_to_node :    fpunode -> UN.node;
val fpunode2_to_unode2: (fpunode * fpunode) -> (UN.unode * UN.unode);
val fpunode2_to_node2:  (fpunode * fpunode) -> (UN.node  * UN.node);

end;