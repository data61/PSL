(*  Title:      Containers/Compatibility_Containers_Regular_Sets.thy
    Author:     Andreas Lochbihler, ETH Zurich *)

section \<open>Compatibility with Regular-Sets\<close>

theory Compatibility_Containers_Regular_Sets imports
  Containers
  "Regular-Sets.Regexp_Method"
begin

text \<open>
  Adaptation theory to make \<open>regexp\<close> work when @{theory Containers.Containers} are loaded.

  Warning: Each invocation of \<open>regexp\<close> takes longer than without @{theory Containers.Containers}
  because the code generator takes longer to generate the evaluation code for \<open>regexp\<close>.
\<close>

datatype_compat rexp
derive ceq rexp
derive ccompare rexp
derive (choose) set_impl rexp

notepad begin
fix r s :: "('a \<times> 'a) set"
have "(r \<union> s^+)^* = (r \<union> s)^*" by regexp
end

end

