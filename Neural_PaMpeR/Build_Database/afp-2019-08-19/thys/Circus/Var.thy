section \<open>UTP variables\<close>

theory Var
imports Main
begin

text \<open>UTP variables are characterized by two functions, $select$ and $update$. 
        The variable type is then defined as a tuple ($select$ * $update$).\<close>

type_synonym ('a, 'r) var = "('r \<Rightarrow> 'a) * (('a \<Rightarrow> 'a) \<Rightarrow> 'r \<Rightarrow> 'r)"

text \<open>The $lookup$ function returns the corrsponding $select$ function of a variable.\<close>

definition lookup :: "('a, 'r) var \<Rightarrow> 'r \<Rightarrow> 'a"
  where "lookup f \<equiv> (fst f)"

text \<open>The $assign$ function uses the $update$ function of a variable to update its value.\<close>

definition assign :: "('a, 'r) var \<Rightarrow> 'a \<Rightarrow> 'r \<Rightarrow> 'r"
  where "assign f v \<equiv> (snd f) (\<lambda> _ . v)"

text \<open>The $VAR$ function allows to retrieve a variable given its name.\<close>

syntax "_VAR" :: "id \<Rightarrow> ('a, 'r) var"  ("VAR _")
translations "VAR x" => "(x, _update_name x)"

end
