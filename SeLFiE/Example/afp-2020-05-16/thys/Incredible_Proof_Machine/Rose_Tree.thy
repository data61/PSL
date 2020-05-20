theory Rose_Tree
imports Main "HOL-Library.Sublist"
begin

text \<open>For theory \<open>Incredible_Trees\<close> we need rose trees; this theory contains
the generally useful part of that development.\<close>

subsubsection \<open>The rose tree data type\<close>


datatype 'a rose_tree = RNode (root: 'a) (children:  "'a rose_tree list")

subsubsection \<open>The set of paths in a rose tree\<close>

text \<open>Too bad that @{command inductive_set} does not allow for varying parameters...\<close>

inductive it_pathsP :: "'a rose_tree \<Rightarrow> nat list \<Rightarrow> bool"  where
   it_paths_Nil: "it_pathsP t []"
 | it_paths_Cons: "i < length (children t) \<Longrightarrow> children t ! i = t' \<Longrightarrow> it_pathsP t' is \<Longrightarrow> it_pathsP t (i#is)"

inductive_cases it_pathP_ConsE: "it_pathsP t (i#is)"

inductive_cases it_pathP_RNodeE: "it_pathsP (RNode r ants) is"

definition it_paths:: "'a rose_tree \<Rightarrow> nat list set"  where
  "it_paths t = Collect (it_pathsP t)"

lemma it_paths_eq [pred_set_conv]: "it_pathsP t = (\<lambda>x. x \<in> it_paths t)"
 by(simp add: it_paths_def)

lemmas it_paths_intros [intro?] = it_pathsP.intros[to_set]
lemmas it_paths_induct [consumes 1, induct set: it_paths] = it_pathsP.induct[to_set]
lemmas it_paths_cases [consumes 1, cases set: it_paths] = it_pathsP.cases[to_set]
lemmas it_paths_ConsE = it_pathP_ConsE[to_set]
lemmas it_paths_RNodeE = it_pathP_RNodeE[to_set]
lemmas it_paths_simps = it_pathsP.simps[to_set]

lemmas it_paths_intros(1)[simp]

lemma it_paths_RNode_Nil[simp]: "it_paths (RNode r []) = {[]}"
  by (auto elim: it_paths_cases)

lemma it_paths_Union: "it_paths t \<subseteq> insert [] (Union (((\<lambda> (i,t). ((#) i) ` it_paths t) ` set (List.enumerate (0::nat) (children t)))))"
  apply (rule)
  apply (erule it_paths_cases)
  apply (auto intro!: bexI simp add: in_set_enumerate_eq)
  done

lemma finite_it_paths[simp]: "finite (it_paths t)"
  by (induction t) (auto intro!:  finite_subset[OF it_paths_Union]  simp add: in_set_enumerate_eq)

subsubsection \<open>Indexing into a rose tree\<close>

fun tree_at :: "'a rose_tree \<Rightarrow> nat list \<Rightarrow> 'a rose_tree" where
  "tree_at t [] = t"
| "tree_at t (i#is) = tree_at (children t ! i) is"

lemma it_paths_SnocE[elim_format]:
  assumes "is @ [i] \<in> it_paths t"
  shows "is \<in> it_paths t \<and> i < length (children (tree_at t is))"
using assms
by (induction "is" arbitrary: t)(auto intro!: it_paths_intros elim!: it_paths_ConsE)


lemma it_paths_strict_prefix:
  assumes "is \<in> it_paths t"
  assumes "strict_prefix is' is"
  shows "is' \<in> it_paths t"
proof-
  from assms(2)
  obtain is'' where "is = is' @ is''" using strict_prefixE' by blast
  from assms(1)[unfolded this]
  show ?thesis
    by(induction is' arbitrary: t) (auto elim!: it_paths_ConsE intro!: it_paths_intros)
qed

lemma it_paths_prefix:
  assumes "is \<in> it_paths t"
  assumes "prefix is' is"
  shows "is' \<in> it_paths t"
using assms it_paths_strict_prefix strict_prefixI by fastforce

lemma it_paths_butlast:
  assumes "is \<in> it_paths t"
  shows "butlast is \<in> it_paths t"
using assms prefixeq_butlast by (rule it_paths_prefix)

lemma it_path_SnocI:
  assumes "is \<in> it_paths t" 
  assumes "i < length (children (tree_at t is))"
  shows "is @ [i] \<in> it_paths t"
  using assms
  by (induction t arbitrary: "is" i)
     (auto 4 4  elim!: it_paths_RNodeE intro: it_paths_intros)


end
