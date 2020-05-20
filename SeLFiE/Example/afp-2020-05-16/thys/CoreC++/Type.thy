(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Based on the Jinja theory Common/Decl.thy by David von Oheimb and Tobias Nipkow 
*)

section \<open>CoreC++ types\<close>

theory Type imports Auxiliary begin


type_synonym cname = string \<comment> \<open>class names\<close>
type_synonym mname = string \<comment> \<open>method name\<close>
type_synonym vname = string \<comment> \<open>names for local/field variables\<close>
 
definition this :: vname where
  "this \<equiv> ''this''"

\<comment> \<open>types\<close>
datatype ty
  = Void          \<comment> \<open>type of statements\<close>
  | Boolean
  | Integer
  | NT            \<comment> \<open>null type\<close>
  | Class cname   \<comment> \<open>class type\<close>

datatype base  \<comment> \<open>superclass\<close>
  = Repeats cname  \<comment> \<open>repeated (nonvirtual) inheritance\<close>
  | Shares cname   \<comment> \<open>shared (virtual) inheritance\<close>

primrec getbase :: "base \<Rightarrow> cname" where
  "getbase (Repeats C) = C"
| "getbase (Shares C)  = C"

primrec isRepBase :: "base \<Rightarrow> bool" where
  "isRepBase (Repeats C) = True"
| "isRepBase (Shares C) = False"

primrec isShBase :: "base \<Rightarrow> bool" where
  "isShBase(Repeats C) = False"
| "isShBase(Shares C) = True"

definition is_refT :: "ty \<Rightarrow> bool" where
  "is_refT T  \<equiv>  T = NT \<or> (\<exists>C. T = Class C)"

lemma [iff]: "is_refT NT"
by(simp add:is_refT_def)

lemma [iff]: "is_refT(Class C)"
by(simp add:is_refT_def)

lemma refTE:
  "\<lbrakk>is_refT T; T = NT \<Longrightarrow> Q; \<And>C. T = Class C \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (auto simp add: is_refT_def)

lemma not_refTE:
  "\<lbrakk> \<not>is_refT T; T = Void \<or> T = Boolean \<or> T = Integer \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (cases T, auto simp add: is_refT_def)

type_synonym 
  env  = "vname \<rightharpoonup> ty"

end

