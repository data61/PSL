(*
 * Term_Table_for_Abduction.ML
 *
 * Authors:
 *   Yutaka Nagashima
 *)
(*** signature TERM_TABLE_FOR_ABDUCTION ***)
signature TERM_TABLE_FOR_ABDUCTION =
sig

type table;
type path;
type paths;

val update_ancestors_of: (table * path -> table) -> table -> path -> table;
val get_children       : table -> ints -> paths;
val get_descendents    : table -> path -> paths;
val rm_descendents     : table -> path -> table;

type node;
type unode;
val update_node_of_unode      : node -> unode -> unode;
val update_print_of_unode     : string -> unode -> unode;
val update_inner_path_of_unode: path -> unode -> unode;

val update_tag_of_unode                          : Proof.context -> unode -> unode;
val update_unode                                 : Proof.context -> unode -> string -> node -> unode;
val update_unode_in_table                        : Proof.context -> unode -> string -> node -> table -> table;
val update_print_of_unode_because_of_its_children: unode -> table -> table;
val update_print_of_path_because_of_its_children : table -> path -> table;
val update_unode_then_its_ancestors_in_table     : table -> path -> unode -> table;
val new_unode_of_fvar                            : int -> path -> unode;

end;

(*** structure Term_Table_for_Abduction ***)
structure Term_Table_for_Abduction: TERM_TABLE_FOR_ABDUCTION =
struct

open Unique_Node;

type table = Inner_Path_To_Unode.path_to_unode_table;
type path  = ints;
type paths = ints list;

fun update_ancestors_of _                                (table:table) [] = table
  | update_ancestors_of (update:(table * path) -> table) (table:table) (path:path) =
    let
      val parent_path = Utils.init path;
      val is_defined  = Inner_Path_To_Unode.defined table parent_path: bool;
      val _ = if is_defined then () else error "update_ancestors failed. undefined unique_node.";
      val updated_table = update (table, parent_path): table;
    in
      update_ancestors_of update  updated_table (parent_path)
    end;

fun get_children' (path_to_unode_table:Inner_Path_To_Unode.path_to_unode_table) (parent_path:path) (nth_child:int) (acc:paths) =
  let
    val nth_child_is_defined = Inner_Path_To_Unode.defined path_to_unode_table (parent_path @ single nth_child): bool;
    val result =
      if   nth_child_is_defined
      then get_children' path_to_unode_table parent_path (nth_child + 1) (acc @ single (parent_path @ single nth_child))
      else acc
  in
    result         
  end;

fun get_children (path_to_unode_table:table) (parent_path:path) =
  get_children' path_to_unode_table parent_path 0 []: ints list;


fun get_descendents (table:table) (path:path): paths =
    let
      val children_paths = get_children table path: ints list;
      val other_descendents_paths = map (get_descendents table) children_paths: ints list list;
    in
      children_paths @ flat other_descendents_paths: ints list
    end;

fun rm_descendents (table:table) (path:path): table =
    let
      val descendents_paths = get_descendents table path: ints list;
      val new_table = fold Inner_Path_Table.delete_safe descendents_paths table: table
    in
      new_table
    end;

fun update_node_of_unode (new_node:node) ({print, inner_path, tag, ...}: unode) =
{
 node       = new_node,
 print      = print,
 inner_path = inner_path,
 tag        = tag
}: unode;

fun update_print_of_unode (new_print:string) ({node, inner_path, tag,...}:Unique_Node.unode) =
{
 node       = node,
 print      = new_print,
 inner_path = inner_path,
 tag        = tag
}: unode;

fun update_inner_path_of_unode (new_inner_path:ints) ({node, print, tag,...}:Unique_Node.unode) =
{
 node       = node,
 print      = print,
 inner_path = new_inner_path,
 tag        = tag
}: unode;


fun update_tag_of_unode (ctxt:Proof.context) (unode as {node, print, inner_path, tag}:unode) =
    case node of (NC (cname, typ)) =>
      let
        val new_tag = {
          part_of_prem           = #part_of_prem  tag                                                      : bool,
          part_of_cncl           = #part_of_cncl  tag                                                      : bool,
          is_premise             = #is_premise    tag                                                      : bool,
          is_conclusion          = #is_conclusion tag                                                      : bool,
          defined_with_n_clauses = SOME (SeLFiE_Util.ctxt_n_cname_to_number_of_defining_clauses ctxt cname): int option,
          is_defined_with        = SOME (Definition_Pattern.get_command ctxt cname)                        : Definition_Pattern.command option,
          take_n_params          = SOME (Isabelle_Utils.count_numb_of_args_of_fun_typ typ)                 : int option
        }: tag;
      in
        {node       = node,
         print      = print,
         inner_path = inner_path,
         tag        = new_tag
        }: Unique_Node.unode
      end
| _ => unode;

fun update_unode (ctxt:Proof.context) (old_unode:unode) (new_print:string) (new_node:node) =
   update_node_of_unode new_node old_unode
|> update_print_of_unode new_print
|> update_tag_of_unode ctxt: unode;

fun update_unode_in_table (ctxt:Proof.context) (old_unode:unode) (new_print:string) (new_node:node) (old_table:table) =
  let
    val new_unode = update_unode ctxt old_unode new_print new_node: unode;
    val path      = #inner_path old_unode: ints;
    val new_table = Inner_Path_Table.update (path, new_unode) old_table;
  in
    new_table: table
  end;

fun update_print_of_unode_because_of_its_children (unode as {node, inner_path, ...}: unode) (table:table): table =
  case node of
    NA =>
      let
        val children_paths  = get_children table inner_path                            : ints list;
        val sorted_paths    = sort (list_ord int_ord) children_paths                   : ints list;
        val children        = map (the o Inner_Path_To_Unode.lookup table) sorted_paths: unode list;
        val children_prints = map (enclose "(" ")" o #print) children                  : strings;
        val func_print      = hd children_prints                                       : string;
        val args_prints     = tl children_prints                                       : strings;
        val new_print       =
            if func_print = "(Pure.imp)"
            then String.concatWith " \<Longrightarrow> " args_prints
            else if func_print = "(Pure.conjunction)"
            then String.concatWith " &&& " args_prints
            else String.concatWith " " children_prints;
        val new_unode      = update_print_of_unode new_print unode;
        val new_graph      = Inner_Path_Table.update (inner_path, new_unode) table
      in
        new_graph
      end
  | NL vname_typ_pairs =>
      let
        val vnames    = map fst vname_typ_pairs: strings;
        val lambdas   = "\<lambda> " ^ String.concatWith " " vnames ^ ". ";
        val child     = Inner_Path_To_Unode.lookup table (inner_path @ [0]) |> the: unode;
        val new_print = lambdas ^ #print child;
        val new_unode = update_print_of_unode new_print unode;
        val new_graph = Inner_Path_Table.update (inner_path, new_unode) table
      in
        new_graph
      end
  | _ => table;

fun update_print_of_path_because_of_its_children (table:table) (path:path): table =
  let
    val is_defined = Inner_Path_To_Unode.defined table path: bool;
    val _          = if is_defined then () else error "update_print_of_path_because_of_its_children failed. undefined unique_node.";
    val unode      = Inner_Path_To_Unode.lookup table path |> the: unode;
    val new_table  = update_print_of_unode_because_of_its_children unode table;
  in
    new_table
  end;

fun update_unode_then_its_ancestors_in_table (table:table) (path:path) (unode:unode) =
  let
    val is_defined        = Inner_Path_To_Unode.defined table path: bool;
    val _                 = if is_defined then () else error "update_print_of_path_because_of_its_children failed. undefined unique_node.";
    val table_w_new_unode = Inner_Path_Table.update (path, unode) table: table;
    val has_parent        = length path > 0                            : bool;
    val table             = if has_parent
                            then update_ancestors_of (uncurry update_print_of_path_because_of_its_children) table_w_new_unode path: table
                            else table_w_new_unode;
  in
    table
  end;

fun new_unode_of_fvar (int:int) (path:path) =
  let
    val print = "var_" ^ Int.toString int;
    val node  = NF (print, dummyT);
    val dummy_tag = {
      part_of_prem           = true: bool,
      part_of_cncl           = true: bool,
      is_premise             = true: bool,
      is_conclusion          = true: bool,
      defined_with_n_clauses = NONE: int option,
      is_defined_with        = NONE: Definition_Pattern.command option,
      take_n_params          = NONE: int option
    };
    val unode = {node = node, print = print, inner_path = path, tag = dummy_tag}: unode;
  in
    unode
  end;

end;