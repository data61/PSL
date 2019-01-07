(*  Title:      PSL/Term_Table_Struct.ML
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

(*** Term_Table ***)
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

end;

(* path_ord: This definition is more or less arbitrary. *)
fun path_ord' ([],    []   ) = EQUAL
  | path_ord' (_,     []   ) = GREATER
  | path_ord' ([],     _   ) = LESS
  | path_ord' (x::xs, y::ys) = case Int.compare (x, y) of
      EQUAL => path_ord' (xs, ys)
    | diff  => diff;

fun path_ord (ints1, ints2) = path_ord' (ints1, ints2);

type path = ints;
structure One_Term = Table(type key = path val ord = path_ord): TABLE;

val list_fold = fold;
local

open One_Term;

in

type trm_table     = Term_Table.unique_node_wo_path table;
type trm_table_aux = Term_Table.unique_node_w_auxiliary_wo_path table;

fun mk_pair (unode:Term_Table.unique_node) =
 (#path unode                  : path,
  {node = #node unode          : Term_Table.node,
   print = #print unode: Term_Table.print}: Term_Table.unique_node_wo_path);

fun to_be_folded (key_val_pair:(path * 'a)) (table: 'a table) = (
update_new key_val_pair table
)
;

fun list_to_table (key_val_pairs: (path * 'a) list) = list_fold to_be_folded key_val_pairs empty; 

fun unique_nodes_to_trm_table (unodes:Term_Table.unique_nodes) = List.map mk_pair unodes |> list_to_table;

val unique_node_wo_path_to_unique_node_w_auxiliary = undefined: Term_Table.unique_node_wo_path table -> Proof.state -> trm_table_aux;

type abs_pstate =
  {fst_subg: Term_Table.unique_node_wo_path table,
   usings  : Term_Table.unique_node_wo_path table list};

type abs_pstate_w_aux =
  {fst_subg: trm_table_aux,
   usings  : trm_table_aux list};

end;