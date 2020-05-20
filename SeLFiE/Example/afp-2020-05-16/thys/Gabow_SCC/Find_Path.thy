section \<open>Safety-Property Model-Checker\label{sec:find_path}\<close>
theory Find_Path
imports
  CAVA_Automata.Digraph
  CAVA_Base.CAVA_Code_Target
begin
  section \<open>Finding Path to Error\<close>
  text \<open>
    This function searches a graph and a set of start nodes for a reachable
    node that satisfies some property, and returns a path to such a node iff it
    exists.
\<close>
  definition "find_path E U0 P \<equiv> do {
    ASSERT (finite U0);
    ASSERT (finite (E\<^sup>*``U0));
    SPEC (\<lambda>p. case p of 
      Some (p,v) \<Rightarrow> \<exists>u0\<in>U0. path E u0 p v \<and> P v \<and> (\<forall>v\<in>set p. \<not> P v)
    | None \<Rightarrow> \<forall>u0\<in>U0. \<forall>v\<in>E\<^sup>*``{u0}. \<not>P v)
    }"

  lemma find_path_ex_rule:
    assumes "finite U0"
    assumes "finite (E\<^sup>*``U0)"
    assumes "\<exists>v\<in>E\<^sup>*``U0. P v"
    shows "find_path E U0 P \<le> SPEC (\<lambda>r. 
      \<exists>p v. r = Some (p,v) \<and> P v \<and> (\<forall>v\<in>set p. \<not>P v) \<and> (\<exists>u0\<in>U0. path E u0 p v))"
    unfolding find_path_def
    using assms
    by (fastforce split: option.splits) 

  subsection \<open>Nontrivial Paths\<close>

  definition "find_path1 E u0 P \<equiv> do { 
    ASSERT (finite (E\<^sup>*``{u0}));
    SPEC (\<lambda>p. case p of 
      Some (p,v) \<Rightarrow> path E u0 p v \<and> P v \<and> p\<noteq>[]
    | None \<Rightarrow> \<forall>v\<in>E\<^sup>+``{u0}. \<not>P v)}"

  lemma (in -) find_path1_ex_rule:
    assumes "finite (E\<^sup>*``{u0})"
    assumes "\<exists>v\<in>E\<^sup>+``{u0}. P v"
    shows "find_path1 E u0 P \<le> SPEC (\<lambda>r. 
      \<exists>p v. r = Some (p,v) \<and> p\<noteq>[] \<and> P v \<and> path E u0 p v)"
    unfolding find_path1_def
    using assms
    by (fastforce split: option.splits) 

end
