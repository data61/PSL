(*  Title:      PSL/Term_Table_Sig.ML
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

(*** TERM_TABLE ***)
signature TERM_TABLE =
sig

(** from Unique_Node_Struct **)

datatype node = (*TODO: This should be Unique_Node.node.*)
  NC of (string * typ)    (*Const*)
| NF of (string * typ)    (*Free*)
| NV of (indexname * typ) (*Var*)
| NB of  int              (*Bound*)
| NL of (string * typ)    (*Abs (Lambda Abstraction)*)
| NA                      (*$   (Application)*)

type print        = string  (*TODO: This should be Unique_Node.print.*)
type path         = int list(*TODO: This should be Unique_Node.path. *)

(* unique_node *)(*TODO: This should be Unique_Node.unique_node.*)
type unique_node =
  {node : node,
   print: print,
   path : path};

type unique_nodes = unique_node list;

(** Original in Term_Table **)
(* term_table represents a proof obligation with its surrounding proof state. *)
val path_ord: (path * path) -> order;

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
type unique_node_w_auxiliary_wo_path =
(* We do not need a path anymore within a node
 * because a path is used as an unique identifier to a unique node. *)
 {node : node,
  print: print,
  rcsv: bool option,
  pttrn: pttrn_of_a_cnst option,
  cmmnd: command option};

val unique_node_to_unique_node_w_auxiliary: unique_node -> unique_node_w_auxiliary_wo_path;

include TABLE;

type unique_node_wo_path =
  {node : node,
   print: print};
            
val unique_nodes_to_a_table: unique_nodes -> unique_node_wo_path table;

val unique_node_wo_path_to_unique_node_w_auxiliary: unique_node_wo_path table -> unique_node_w_auxiliary_wo_path table;

end;