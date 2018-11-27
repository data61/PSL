(*  Title:      PSL/DInduct_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Infrastructure to construct various induct methods.
It is similar to Dynamic (Induct) in PSL but tailored for MiLkMaId.
*)
signature DYNAMIC_INDUCT =
sig

datatype modifier = 
  Ind  of Transform.unique_node_w_print
| Arb  of Transform.unique_node_w_print
| Rule of string;

type modifiers = modifier list;

val unique_np_to_ons : Transform.unique_node_w_prints -> modifier;
val unique_np_to_arbs: Transform.unique_node_w_prints -> modifiers;
val strs_to_rules    : strings              -> modifiers;
val order            : modifiers -> (modifiers * modifiers * modifiers);
val same_mod         : (modifier  * modifier ) -> bool;
val same_mods        : (modifiers * modifiers) -> bool;
val filter_inds      : modifiers -> modifiers;
val filter_arbs      : modifiers -> modifiers;
val filter_rules     : modifiers -> modifiers;

end;