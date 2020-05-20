theory "Identifiers"
imports Complex_Main
begin
subsection \<open>Identifier Namespace Configuration\<close>

text \<open>Different configurations are possible for the namespace of identifiers. Finite support is the only important aspect of it.\<close>

(* Identifiers, easiest finite case *)
type_synonym ident = char

(* Identifiers, bigger finite case with longer identifiers *)
(*
definition max_str:"MAX_STR = 1"
typedef ident = "{s::string. size s \<le> MAX_STR}"
  morphisms Rep_ident Abs_ident
  apply(auto)
  apply(rule exI[where x=Nil])
  by(auto simp add: max_str)

setup_lifting  ident.type_definition_ident 

lift_definition ilength::"ident \<Rightarrow> nat" is size done

lemma ident_bounded_length: "ilength x \<le> MAX_STR"
  apply (transfer fixing: s)
  apply (auto)
  done 

lemma finite_identifiers [simp]: "finite {x:ident . True}"
using ident_bounded_length 
  
lifting_update ident.lifting
lifting_forget ident.lifting
*)

text \<open>The identifier used for the replacement marker in uniform substitutions\<close>
abbreviation dotid:: "ident"
where "dotid \<equiv> CHR ''.''"

end
