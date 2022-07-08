theory Top_Down_Conjecturing
  imports "PSL.PSL"
begin

ML\<open> signature TOP_DOWN_CONJECTURING =
sig

datatype top_down_conjecturing = (*exemplary cases*)
  Term_Generalisation (*Prod/05 Prod/06*)
| Extension
| Specialisation
| Unary_Function_Application
| Swap_Unequal_Arguments (*Prod/01*)(*Should I consider this as a bottom-up conjecturing? cf: Prod/03*)
| Remove_Assumption (*Prod/07*)(*Can be done by thin_tac, but better as an introduction rule.*)
| Existential_Quantifier_Instantiation (*TODO: find an example.*)

val top_down_conjecturing: top_down_conjecturing -> Proof.state -> Proof.state

end;
\<close>

end