(*** TRANSFORM_STRUCT ***)
structure Transform =
struct

(** term as syntax tree **)
(* The overall work-flow is:
 * term                              ---->
 * trm_w_prnt                        ---->
 * futrm_w_prnt                      ---->
 * futrm_w_prnt_n_path               ---->    
 * One_Term: TABLE with node_w_print ---->
 * One_Term: TABLE with node_w_auxiliary
 *)

(* print: the printed format of a sub-tree in the syntax tree of a term. *)
datatype print = Print of string;

(* trm_w_prnt: term with print *)
datatype trm_w_prnt =
  C_Prnt of string * typ        * print (*Const*)
| F_Prnt of string * typ        * print (*Free*)
| V_Prnt of indexname * typ     * print (*Var*)
| B_Prnt of int                 * print (*Bound*)
| L_Prnt of string * typ * term * print (*Abs (Lambda Abstraction)*)
| A_Prnt of term * term         * print;(*$   (Application)*)

(* trm_to_trm_w_prnt *)
val trm_to_trm_w_prnt = undefined: term -> trm_w_prnt;

(* utrm_w_prnt: un-curried term with print *)
datatype utrm_w_prnt =
  UC_Prnt of string * typ                   * print
| UF_Prnt of string * typ                   * print
| UV_Prnt of indexname * typ                * print
| UB_Prnt of int                            * print
| UL_Prnt of string * typ * utrm_w_prnt     * print
| UA_Prnt of utrm_w_prnt * utrm_w_prnt list * print;

(* trm_w_prnt_to_utrm_w_prnt *)
val trm_w_prnt_to_utrm_w_prnt = undefined: trm_w_prnt -> utrm_w_prnt;

(* 
 * Isabelle's functions for Hereditary Harrop Formula, such as Drule.norm_hhf, are not helpful here:
 * Hereditary Harrop Formula still involve possibly nested applications of binary meta-implications,
 * thus introducing the un-fair depth measure among premises of meta-implications.
 * We should flatten terms after introducing uncurrying forms because flattening nested pure-implications
 * requires uncurried terms.
 *)

(* futrm_w_prnt: un-curried flattened term with print *)
datatype futrm_w_prnt =
  FUC_Prnt of string * typ                     * print
| FUF_Prnt of string * typ                     * print
| FUV_Prnt of indexname * typ                  * print
| FUB_Prnt of int                              * print
| FUL_Prnt of string * typ * futrm_w_prnt      * print
| FUA_Prnt of futrm_w_prnt * futrm_w_prnt list * print;

(* utrm_w_prnt_to_utrm_w_prnt *)
val utrm_w_prnt_to_utrm_w_prnt = undefined: trm_w_prnt -> utrm_w_prnt;

(* un-curried flattened term with print and path*)
type ints = int list;

datatype path  = Path of ints;
type     paths = path list;

(* futrm_w_prnt_n_path: un-curried flattened term with print and path to each node*)
datatype futrm_w_prnt_n_path =
  UFC_Prnt_n_Path of (string * typ                             ) * print * path
| UFF_Prnt_n_Path of (string * typ                             ) * print * path
| UFV_Prnt_n_Path of (indexname * typ                          ) * print * path
| UFB_Prnt_n_Path of  int                                        * print * path
| UFL_Prnt_n_Path of (string * typ * futrm_w_prnt_n_path       ) * print * path
| UFA_Prnt_n_Path of (futrm_w_prnt_n_path * futrm_w_prnt_n_path) * print * path;

(** term as Table  **)
datatype node =
  NC of (string * typ)    (*Const*)
| NF of (string * typ)    (*Free*)
| NV of (indexname * typ) (*Var*)
| NB of  int              (*Bound*)
| NL of (string * typ)    (*Abs (Lambda Abstraction)*)
| NA                      (*$   (Application)*)

datatype node_w_print = Node_Print of {node: node, print:print};
type     node_w_prints = node_w_print list;
val path_ord = undefined: (path * path) -> order;

structure One_Term = Table(type key = path val ord = path_ord): TABLE;

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
type node_w_auxiliary =
 {node : node,
  print: print,
  rcsv: bool option,
  pttrn: pttrn_of_a_cnst option,
  cmmnd: command option};

(*
 * datatype location = Fst_Subg | Chnd_Fct of int;
 * datatype key      = Node_Location of (location * path);
 *)

end;