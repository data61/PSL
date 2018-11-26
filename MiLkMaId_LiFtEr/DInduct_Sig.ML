signature DYNAMIC_INDUCT =
sig
datatype unique_node_w_print  = Node_Print of {node: Transform.node, print:Transform.print};
type     unique_node_w_prints = unique_node_w_print list;

(*To be used in the new dynamic induct.*)
val nodes_w_print_to_unique_nodes_w_print: Transform.node_w_prints -> unique_node_w_prints;
val unique_node_w_print_to_paths         : unique_node_w_print -> Transform.paths;
val unique_nodes_w_print_to_pathss       : unique_node_w_prints -> Transform.paths list;
val unique_nodes_n_print_to_pathss       : (unique_node_w_prints * Transform.paths list);(*Use: AList.update*)
datatype unique_node_id = Unique_Node_Id of int;         
                          
datatype rule_name = Rule_Name of string;

(*TIP: use functions from AList, such as AList.update, for name_space.*)
datatype name_space = Name_Space of
 {subtrm:     (int * Transform.path) list,
  subtrm_occ: (int * unique_node_id) list,
  rule:       (int * rule_name)      list};

datatype modifier = 
  Ind  of unique_node_w_print
| Arb  of unique_node_w_print
| Rule of string;

type modifiers = modifier list;

val unique_np_to_ons : unique_node_w_prints -> modifier;
val unique_np_to_arbs: unique_node_w_prints -> modifiers;
val strs_to_rules    : strings              -> modifiers;
val order            : modifiers -> (modifiers * modifiers * modifiers);
val same_mod         : (modifier  * modifier ) -> bool;
val same_mods        : (modifiers * modifiers) -> bool;
val filter_inds      : modifiers -> modifiers;
val filter_arbs      : modifiers -> modifiers;
val filter_rules     : modifiers -> modifiers;

end;