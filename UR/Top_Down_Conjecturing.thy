theory Top_Down_Conjecturing
  imports "../PSL/PSL"
begin

ML\<open> signature TOP_DOWN_CONJECTURING =
sig

datatype top_down_conjecturing =
  Term_Generalisation
| Extension
| Specialisation
| Unary_Function_Application;

val top_down_conjecturing: top_down_conjecturing -> Proof.state -> Proof.state

end;
\<close>

ML\<open>
\<close>

end