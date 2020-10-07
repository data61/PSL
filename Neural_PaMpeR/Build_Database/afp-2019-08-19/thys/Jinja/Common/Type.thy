(*  Title:      Jinja/Common/Type.thy

    Author:     David von Oheimb, Tobias Nipkow
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>Jinja types\<close>

theory Type imports Auxiliary begin

type_synonym cname = string \<comment> \<open>class names\<close>
type_synonym mname = string \<comment> \<open>method name\<close>
type_synonym vname = string \<comment> \<open>names for local/field variables\<close>

definition Object :: cname
where
  "Object \<equiv> ''Object''"

definition this :: vname
where
  "this \<equiv> ''this''"

\<comment> \<open>types\<close>
datatype ty
  = Void          \<comment> \<open>type of statements\<close>
  | Boolean
  | Integer
  | NT            \<comment> \<open>null type\<close>
  | Class cname   \<comment> \<open>class type\<close>

definition is_refT :: "ty \<Rightarrow> bool"
where
  "is_refT T  \<equiv>  T = NT \<or> (\<exists>C. T = Class C)"

lemma [iff]: "is_refT NT"
(*<*)by(simp add:is_refT_def)(*>*)

lemma [iff]: "is_refT(Class C)"
(*<*)by(simp add:is_refT_def)(*>*)

lemma refTE:
  "\<lbrakk>is_refT T; T = NT \<Longrightarrow> P; \<And>C. T = Class C \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
(*<*)by (auto simp add: is_refT_def)(*>*)

lemma not_refTE:
  "\<lbrakk> \<not>is_refT T; T = Void \<or> T = Boolean \<or> T = Integer \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
(*<*)by (cases T, auto simp add: is_refT_def)(*>*)

end
