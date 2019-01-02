(*  Title:      PSL/Unique_Node_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
  term                              === trm_w_prnt_to_utrm_w_prnt ==================> (* in this file *)
  trm_w_prnt                        === utrm_w_prnt_to_utrm_w_prnt =================> (* in this file *)
  utrm_w_prnt                       === utrm_w_prnt_to_utrm_w_prnt =================> (* in this file *)
  futrm_w_prnt                      === futrm_w_prnt_to_futrm_w_prnt_n_path ========> (* in this file *)
  futrm_w_prnt_n_path               === futrm_w_prnt_n_path_to_unique_nodes ========> (* in this file *)
  unique_nodes                      === unique_nodes_to_unique_nodes_w_auxiliary ===> (* Term_Table_Sig.ML *)
  nodes_w_auxiliary                                                                   (* Term_Table_Sig.ML *)
*)

(*** UNIQUE_NODE ***)
signature UNIQUE_NODE =
sig

(** term as syntax tree **)

(* print: the printed format of a sub-tree in the syntax tree of a term. *)
datatype print = Print of string;

(* trm_w_prnt: term with print *)
datatype trm_w_prnt =
  C_Prnt of string * typ              * print (*Const*)
| F_Prnt of string * typ              * print (*Free*)
| V_Prnt of indexname * typ           * print (*Var*)
| B_Prnt of int                       * print (*Bound*)
| L_Prnt of string * typ * trm_w_prnt * print (*Abs (Lambda Abstraction)*)
| A_Prnt of trm_w_prnt * trm_w_prnt   * print;(*$   (Application)*)

(* trm_to_trm_w_prnt *)
val trm_to_trm_w_prnt: Proof.context -> term -> trm_w_prnt;

(* utrm_w_prnt: un-curried term with print *)
datatype utrm_w_prnt =
  UC_Prnt of string * typ                   * print
| UF_Prnt of string * typ                   * print
| UV_Prnt of indexname * typ                * print
| UB_Prnt of int                            * print
| UL_Prnt of string * typ * utrm_w_prnt     * print
| UA_Prnt of utrm_w_prnt * utrm_w_prnt list * print;

(* utrms_w_prnt *)
type utrms_w_prnt = utrm_w_prnt list;

(* trm_w_prnt_to_utrm_w_prnt *)
val trm_w_prnt_to_utrm_w_prnt: trm_w_prnt -> utrm_w_prnt;

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

(* utrm_w_prnt_to_futrm_w_prnt *)
val utrm_w_prnt_to_futrm_w_prnt: utrm_w_prnt -> futrm_w_prnt;

type     ints = int list;

(* path *)
datatype path  = Path of ints;

(* paths *)
type     paths = path list;

(* path_ord *)
val path_ord: (path * path) -> order;

(* futrm_w_prnt_n_path: un-curried flattened term with print and path to each node*)
datatype futrm_w_prnt_n_path =
  UFC_Prnt_n_Path of (string * typ                             ) * print * path
| UFF_Prnt_n_Path of (string * typ                             ) * print * path
| UFV_Prnt_n_Path of (indexname * typ                          ) * print * path
| UFB_Prnt_n_Path of  int                                        * print * path
| UFL_Prnt_n_Path of (string * typ * futrm_w_prnt_n_path       ) * print * path
| UFA_Prnt_n_Path of (futrm_w_prnt_n_path * futrm_w_prnt_n_path) * print * path;

(* futrm_w_prnt_to_futrm_w_prnt_n_path *)
val futrm_w_prnt_to_futrm_w_prnt_n_path: futrm_w_prnt -> futrm_w_prnt_n_path;

(* node: un-curried flattened term without print. This constitutes a part of unique_node. *)
datatype node =
  NC of (string * typ)    (*Const*)
| NF of (string * typ)    (*Free*)
| NV of (indexname * typ) (*Var*)
| NB of  int              (*Bound*)
| NL of (string * typ)    (*Abs (Lambda Abstraction)*)
| NA                      (*$   (Application)*)

(* unique_node *)
type unique_node =
  {node : node,
   print: print,
   path : path};

(* unique_nodes *)
type unique_nodes = unique_node list;

(* futrm_w_prnt_n_path_to_unique_nodes *)
val futrm_w_prnt_n_path_to_unique_nodes: futrm_w_prnt_n_path -> unique_nodes;

end;