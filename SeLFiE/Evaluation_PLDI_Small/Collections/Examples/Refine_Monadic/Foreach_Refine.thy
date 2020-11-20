section \<open>\isaheader{Example for Foreach-Loops}\<close>
theory Foreach_Refine
imports 
  Collections.Refine_Dflt_Only_ICF 
begin

text \<open>
  This example presents the usage of the foreach loop.
  We define a simple foreach loop that looks for the largest element with
  a given property. Ordered loops are used to be sure to find the largest one.
\<close>

subsection \<open>Definition\<close>

definition find_max_invar where
  "find_max_invar P S it \<sigma> = 
     (case \<sigma> of None \<Rightarrow> (\<forall>x \<in> S - it. \<not>(P x))
             | Some y \<Rightarrow> (P y \<and> y \<in> S-it \<and> (\<forall>x \<in> S - it - {y}. \<not>(P x))))"

definition find_max :: "('a::{linorder} \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> ('a option) nres" where
  "find_max P S \<equiv> 
   FOREACHoci ((\<ge>)) (find_max_invar P S) S
     (\<lambda>\<sigma>. \<sigma> = None) (\<lambda>x _. RETURN (if P x then Some x else None)) None"

subsection \<open>Correctness\<close>
text \<open>As simple correctness property, we show:
  If the algorithm returns the maximal element satisfying \<open>P\<close>.
\<close>
lemma find_max_correct:
  fixes S:: "'a::{linorder} set"
  assumes "finite S"
  shows "find_max P S \<le> SPEC (\<lambda>\<sigma>. case \<sigma> of None \<Rightarrow> \<forall>x\<in>S. \<not>(P x)
                                          | Some y \<Rightarrow> (P y \<and> y \<in> S \<and> (\<forall>x\<in>S. P x \<longrightarrow> y \<ge> x)))"
  unfolding find_max_def
proof (rule FOREACHoci_rule)
  show "finite S" by fact
next
  show "find_max_invar P S S None" 
  unfolding find_max_invar_def by simp
next
  fix x it \<sigma>
  assume "\<sigma> = None"
         "x \<in> it"
         "it \<subseteq> S"
         "find_max_invar P S it \<sigma>"
         "\<forall>y\<in>it - {x}. y \<le> x"
         "\<forall>y\<in>S - it. x \<le> y"

  from \<open>find_max_invar P S it \<sigma>\<close> \<open>\<sigma> = None\<close> 
  have not_P_others: "\<forall>x\<in>S - it. \<not> P x"
    by (simp add: find_max_invar_def)

  from \<open>x \<in> it\<close> \<open>it \<subseteq> S\<close> have "x \<in> S" by blast

  show "RETURN (if P x then Some x else None) \<le> SPEC (find_max_invar P S (it - {x}))"
    using not_P_others \<open>x \<in> S\<close>
    by (auto simp add: find_max_invar_def)
next
  fix \<sigma>
  assume "find_max_invar P S {} \<sigma>"
  thus "case \<sigma> of None \<Rightarrow> \<forall>x\<in>S. \<not> P x
        | Some y \<Rightarrow> P y \<and> y \<in> S \<and> (\<forall>x\<in>S. P x \<longrightarrow> x \<le> y)"
    by (cases \<sigma>, auto simp add: find_max_invar_def)
next
  fix it \<sigma>
  assume "it \<noteq> {}"
         "it \<subseteq> S"
         "find_max_invar P S it \<sigma>"
         "\<sigma> \<noteq> None"
         "\<forall>x\<in>it. \<forall>y\<in>S - it. x \<le> y"

  from \<open>\<sigma> \<noteq> None\<close> obtain y where \<sigma>_eq[simp]: "\<sigma> = Some y" by auto
  from \<open>find_max_invar P S it \<sigma>\<close> 
    have y_props[simp]: "P y" "y \<in> S" "y \<notin> it" and not_P: "\<forall>x\<in>S - it - {y}. \<not> P x"
    by (simp_all add: find_max_invar_def)
 
  { fix x
    assume "x \<in> S" "P x"
    with not_P have "x \<in> it \<or> x = y" by auto
    with \<open>\<forall>x\<in>it. \<forall>y\<in>S - it. x \<le> y\<close> y_props have "x \<le> y" by auto
  } note less_eq_y = this

  show "case \<sigma> of None \<Rightarrow> \<forall>x\<in>S. \<not> P x
        | Some y \<Rightarrow> P y \<and> y \<in> S \<and> (\<forall>x\<in>S. P x \<longrightarrow> x \<le> y)" 
   by (simp add: find_max_invar_def Ball_def less_eq_y)
qed

subsection \<open>Data Refinement and Determinization\<close>
text \<open>
  Next, we use automatic data refinement and transfer to generate an
  executable algorithm using a red-black-tree. 
\<close>
schematic_goal find_max_impl_refine_aux:
  assumes invar_S: "rs.invar S"
  shows "RETURN (?f) \<le> (find_max P (rs.\<alpha> S))"
  unfolding find_max_def
  by (refine_transfer 
    RBTSetImpl.rs.rev_iterateoi_correct[unfolded set_iterator_rev_linord_def,
    OF invar_S])

concrete_definition find_max_impl for P S uses find_max_impl_refine_aux

lemma find_max_impl_refine:
  assumes invar_S: "rs.invar S"
  shows "RETURN (find_max_impl P S) \<le> (find_max P (rs.\<alpha> S))"
  using assms by (rule find_max_impl.refine)

subsubsection \<open>Executable Code\<close>

lemma find_max_impl_correct :
assumes invar_S: "rs.invar S"
shows "case find_max_impl P S of None \<Rightarrow> \<forall>x\<in>rs.\<alpha> S. \<not>(P x)
                               | Some y \<Rightarrow> (P y \<and> y \<in> (rs.\<alpha> S) 
                                 \<and> (\<forall>x\<in>rs.\<alpha> S. P x \<longrightarrow> y \<ge> x))"
proof -
  note find_max_impl_refine [of S P, OF invar_S]
  also note find_max_correct [OF RBTSetImpl.rs.finite[of S, OF invar_S], of P]
  finally show ?thesis by simp
qed

text \<open>Finally, we can generate code\<close>
export_code find_max_impl checking SML
export_code find_max_impl checking OCaml?
export_code find_max_impl checking Haskell?
export_code find_max_impl checking Scala
  
end
