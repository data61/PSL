(*  Title:      PSL/MiLkMaId_LiFtEr/Unique_Node_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The conversion to transform term to a format more amenable to LiFtEr.
The overall work-flow is:
  term                === trm_to_trm_w_prnt ==========================> (* Unique_Node *)
  trm_w_prnt          === trm_w_prnt_to_utrm_w_prnt ==================> (* Unique_Node *)
  utrm_w_prnt         === utrm_w_prnt_to_futrm_w_prnt ================> (* Unique_Node *)
  futrm_w_prnt        === futrm_w_prnt_to_futrm_w_prnt_n_path ========> (* Unique_Node *)
  futrm_w_prnt_n_path === futrm_w_prnt_n_path_to_unique_nodes ========> (* Unique_Node *)
  unique_nodes        === unique_nodes_to_unique_nodes_w_auxiliary ===> (* Term_Table  *)
  nodes_w_auxiliary
*)

(*** UNIQUE_NODE ***)
signature UNIQUE_NODE =
sig

(** term as syntax tree **)
type print;

(* trm_w_prnt: term with print *)
datatype trm_w_prnt =  
  C_Prnt of string     * typ              * print (*Const*)
| F_Prnt of string     * typ              * print (*Free*)
| V_Prnt of indexname  * typ              * print (*Var*)
| B_Prnt of int        * typ              * print (*Bound*)
| L_Prnt of string     * typ * trm_w_prnt * print (*Abs (Lambda Abstraction)*)
| A_Prnt of trm_w_prnt * trm_w_prnt       * print;(*$   (Application)*)

(* trm_to_trm_w_prnt *)
val trm_to_trm_w_prnt: Proof.context -> term -> trm_w_prnt;

(* utrm_w_prnt: un-curried term with print *)
datatype utrm_w_prnt =
  UC_Prnt of string      * typ               * print
| UF_Prnt of string      * typ               * print
| UV_Prnt of indexname   * typ               * print
| UB_Prnt of int         * typ               * print
| UL_Prnt of string      * typ * utrm_w_prnt * print
| UA_Prnt of utrm_w_prnt * utrm_w_prnt list  * print;

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
  FUC_Prnt of string       * typ                 * print
| FUF_Prnt of string       * typ                 * print
| FUV_Prnt of indexname    * typ                 * print
| FUB_Prnt of int          * typ                 * print
| FUL_Prnt of string       * typ  * futrm_w_prnt * print
| FUA_Prnt of futrm_w_prnt * futrm_w_prnt list   * print;

(* utrm_w_prnt_to_futrm_w_prnt *)
val utrm_w_prnt_to_futrm_w_prnt: utrm_w_prnt -> futrm_w_prnt;

(* path *)
type path  = ints;

val path1_is_above_path2: path -> path -> bool

(* paths *)
type paths = path list;

(* path_ord *)
val path_ord: (path * path) -> order;

(* futrm_w_prnt_n_path: un-curried flattened term with print and path to each node*)
datatype futrm_w_prnt_n_path =
  UFC_Prnt_n_Path of (string    * typ                               ) * print * path
| UFF_Prnt_n_Path of (string    * typ                               ) * print * path
| UFV_Prnt_n_Path of (indexname * typ                               ) * print * path
| UFB_Prnt_n_Path of (int       * typ                               ) * print * path
| UFL_Prnt_n_Path of (string    * typ * futrm_w_prnt_n_path         ) * print * path
| UFA_Prnt_n_Path of (futrm_w_prnt_n_path * futrm_w_prnt_n_path list) * print * path;

(* futrm_w_prnt_to_futrm_w_prnt_n_path *)
val futrm_w_prnt_to_futrm_w_prnt_n_path: futrm_w_prnt -> futrm_w_prnt_n_path;

(* node: un-curried flattened term without print. This constitutes a part of unique_node. *)
datatype node =
  NC of (string    * typ) (*Const*)
| NF of (string    * typ) (*Free*)
| NV of (indexname * typ) (*Var*)
| NB of (int       * typ) (*Bound*)
| NL of (string    * typ) (*Abs (Lambda Abstraction)*)
| NA                      (*$   (Application)*)

datatype node_typ = Node_Typ_NC | Node_Typ_NF | Node_Typ_NV | Node_Typ_NB | Node_Typ_NL | Node_Typ_NA;

val is_NC: node -> bool;
val is_NF: node -> bool;
val is_NV: node -> bool;
val is_NB: node -> bool;
val is_NL: node -> bool;
val is_NA: node -> bool;

val dest_NC: node -> (string    * typ) option;
val dest_NF: node -> (string    * typ) option;
val dest_NV: node -> (indexname * typ) option;
val dest_NB: node -> (int       * typ) option;
val dest_NL: node -> (string    * typ) option;

val node_typ_to_checker: node_typ -> node-> bool;

(* unique_node *)
type unique_node =
  {node : node,
   print: print,
   path : path};

(* unique_nodes *)
type unique_nodes = unique_node list;

(* futrm_w_prnt_n_path_to_unique_nodes *)
val futrm_w_prnt_n_path_to_unique_nodes: futrm_w_prnt_n_path -> unique_nodes;

(* unique_node_wo_path *)
type unique_node_wo_path =
  {node : node,
   print: print};

(* unique_node_w_aux_wo_path *)
type unique_node_w_aux_wo_path =
 {node : node,
  print: print,
  rcsv : bool option,
  pttrn: LiFtEr_Util.pttrn_of_a_const option,
  cmmnd: LiFtEr_Util.command option};

(* unique_node_w_aux *)
type unique_node_w_aux = {path: path, unode_w_aux: unique_node_w_aux_wo_path};

(* unique_node_to_unique_node_w_aux *)
val unique_node_to_unique_node_w_aux: unique_node -> unique_node_w_aux;

end;