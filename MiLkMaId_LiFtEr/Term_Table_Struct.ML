(*  Title:      PSL/Term_Table_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
  term                              === trm_w_prnt_to_utrm_w_prnt ==================> (* in Unique_Node_Struct.ML *)
  trm_w_prnt                        === utrm_w_prnt_to_utrm_w_prnt =================> (* in Unique_Node_Struct.ML *)
  utrm_w_prnt                       === utrm_w_prnt_to_utrm_w_prnt =================> (* in Unique_Node_Struct.ML *)
  futrm_w_prnt                      === futrm_w_prnt_to_futrm_w_prnt_n_path ========> (* in Unique_Node_Struct.ML *)
  futrm_w_prnt_n_path               === futrm_w_prnt_n_path_to_unique_nodes ========> (* in Unique_Node_Struct.ML *)
  unique_nodes                      === unique_nodes_to_unique_nodes_w_auxiliary ===> (* in this file *)
  nodes_w_auxiliary
*)

(**  Term_Table **)
structure Term_Table: TERM_TABLE =

struct

open Unique_Node;

(** pattern **)
datatype left_pttrn  = Var | Cnst;
datatype right_pttrn =
  If
| Case
| Unchanged_In_Rec_Call (*The nth parameter appears as the nth parameter to a recursive call of f on the right hand side.*)
| Changed_In_Rec_Call   (*A part of the nth parameter appears as part of the nth parameter to a recursive call of f.*)
| Sth_Else_In_Rec_Call  (*In a recursive call of f, no part of the nth parameter appears.*);
type     left_pttrns                   = left_pttrn list;
datatype pttrn_for_a_param_in_a_clause = Pttrn_Atom    of right_pttrn * (left_pttrns list);
datatype pttrn_for_a_clause            = Pttrn_Clause  of pttrn_for_a_param_in_a_clause list;
datatype pttrn_for_a_param             = Pttrn_Paramt  of pttrn_for_a_param_in_a_clause list;
datatype pttrn_of_all_clauses          = Pttrn_Clauses of pttrn_for_a_clause list;
datatype pttrn_of_all_params           = Pttrn_Params  of pttrn_for_a_param list;
datatype pttrn_of_a_cnst               = pttrn_of_all_clauses | pttrn_of_all_params;

(* matrix? 'a matrix (= 'a list list) provides more generality.
 * But we only have to tackle this problem for now. So we do not have the necessity for generalization. *)
datatype command = Definition | Fun | Function | Inductive | Primrec | Unknown;

type unique_node_wo_path =
  {node : node,
   print: print};

type unique_node_w_auxiliary_wo_path =
 {node : node,
  print: print,
  rcsv : bool option,
  pttrn: pttrn_of_a_cnst option,
  cmmnd: command option};

val unique_node_to_unique_node_w_auxiliary = undefined;

structure One_Term = Table(type key = path val ord = path_ord): TABLE;
open One_Term;

type trm_table     = unique_node_wo_path table;
type trm_table_aux = unique_node_w_auxiliary_wo_path table;

val unique_nodes_to_trm_table = undefined: unique_nodes -> trm_table;

val unique_node_wo_path_to_unique_node_w_auxiliary = undefined: unique_node_wo_path table -> Proof.state -> trm_table_aux;

datatype rule_name       = Rule_Name of string;
datatype unique_node_id  = UNode_Id of ints;
type     unique_node_ids = unique_node_id list;

(*TIP: use functions from AList, such as AList.update, for name_space.*)
datatype name_space = Name_Space of
 {subtrm:     (int * path)            list,
  subtrm_occ: (int * unique_node_ids) list,
  rule:       (int * rule_name)       list};

type abs_pstate =
  {fst_subg: unique_node_wo_path table,
   usings  : unique_node_wo_path table list};

type abs_pstate_w_aux =
  {fst_subg: trm_table_aux,
   usings  : trm_table_aux list};

end;