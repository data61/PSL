(*  Title:      PSL/LiFtEr/src/DInduct_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Infrastructure to construct various induct methods.
It is similar to Dynamic (Induct) in PSL but tailored for MiLkMaId.
*)
signature DYNAMIC_INDUCT =
sig

datatype modifier = 
  Ind  of string
| Arb  of string
| Rule of string;

type modifiers = modifier list;

val unode_w_aux_wo_path_to_on : Unique_Node.unode_w_aux -> modifier;
val unode_w_aux_wo_path_to_arb: Unique_Node.unode_w_aux -> modifier;
val strs_to_rules             : strings -> modifiers;
val order                     : modifiers -> (modifiers * modifiers * modifiers);
val same_mod                  : (modifier  * modifier ) -> bool;
val same_mods                 : (modifiers * modifiers) -> bool;
val filter_inds               : modifiers -> modifiers;
val filter_arbs               : modifiers -> modifiers;
val filter_rules              : modifiers -> modifiers;

end;