(*
  File: Union_Find.thy
  Author: Bohua Zhan
*)

section \<open>Union find\<close>

theory Union_Find
  imports Partial_Equiv_Rel
begin

text \<open>
  Development follows theory Union\_Find in \cite{Separation_Logic_Imperative_HOL-AFP}.
\<close>

subsection \<open>Representing a partial equivalence relation using rep\_of array\<close>

function (domintros) rep_of where
  "rep_of l i = (if l ! i = i then i else rep_of l (l ! i))" by auto

setup \<open>register_wellform_data ("rep_of l i", ["i < length l"])\<close>
setup \<open>add_backward_prfstep @{thm rep_of.domintros}\<close>
setup \<open>add_rewrite_rule @{thm rep_of.psimps}\<close>
setup \<open>add_prop_induct_rule @{thm rep_of.pinduct}\<close>

definition ufa_invar :: "nat list \<Rightarrow> bool" where [rewrite]:
  "ufa_invar l = (\<forall>i<length l. rep_of_dom (l, i) \<and> l ! i < length l)"

lemma ufa_invarD:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> rep_of_dom (l, i) \<and> l ! i < length l" by auto2
setup \<open>add_forward_prfstep_cond @{thm ufa_invarD} [with_term "?l ! ?i"]\<close>
setup \<open>del_prfstep_thm_eqforward @{thm ufa_invar_def}\<close>

lemma rep_of_id [rewrite]: "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> l ! i = i \<Longrightarrow> rep_of l i = i" by auto2

lemma rep_of_iff [rewrite]:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> rep_of l i = (if l ! i = i then i else rep_of l (l ! i))" by auto2
setup \<open>del_prfstep_thm @{thm rep_of.psimps}\<close>

lemma rep_of_min [rewrite]:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> l ! (rep_of l i) = rep_of l i"
@proof @prop_induct "rep_of_dom (l, i)" @qed

lemma rep_of_induct:
  "ufa_invar l \<and> i < length l \<Longrightarrow>
   \<forall>i<length l. l ! i = i \<longrightarrow> P l i \<Longrightarrow>
   \<forall>i<length l. l ! i \<noteq> i \<longrightarrow> P l (l ! i) \<longrightarrow> P l i \<Longrightarrow> P l i"
@proof @prop_induct "rep_of_dom (l, i)" @qed
setup \<open>add_prop_induct_rule @{thm rep_of_induct}\<close>

lemma rep_of_bound [forward_arg1]:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> rep_of l i < length l"
@proof @prop_induct "ufa_invar l \<and> i < length l" @qed

lemma rep_of_idem [rewrite]:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> rep_of l (rep_of l i) = rep_of l i" by auto2

lemma rep_of_idx [rewrite]: 
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow> rep_of l (l ! i) = rep_of l i" by auto2

definition ufa_\<alpha> :: "nat list \<Rightarrow> (nat \<times> nat) set" where [rewrite]:
  "ufa_\<alpha> l = {(x, y). x < length l \<and> y < length l \<and> rep_of l x = rep_of l y}"

lemma ufa_\<alpha>_memI [backward, forward_arg]:
  "x < length l \<Longrightarrow> y < length l \<Longrightarrow> rep_of l x = rep_of l y \<Longrightarrow> (x, y) \<in> ufa_\<alpha> l"
  by (simp add: ufa_\<alpha>_def)
  
lemma ufa_\<alpha>_memD [forward]:
  "(x, y) \<in> ufa_\<alpha> l \<Longrightarrow> x < length l \<and> y < length l \<and> rep_of l x = rep_of l y"
  by (simp add: ufa_\<alpha>_def)
setup \<open>del_prfstep_thm @{thm ufa_\<alpha>_def}\<close>

lemma ufa_\<alpha>_equiv [forward]: "part_equiv (ufa_\<alpha> l)" by auto2

lemma ufa_\<alpha>_refl [rewrite]: "(i, i) \<in> ufa_\<alpha> l \<longleftrightarrow> i < length l" by auto2

subsection \<open>Operations on rep\_of array\<close>

definition uf_init_rel :: "nat \<Rightarrow> (nat \<times> nat) set" where [rewrite]:
  "uf_init_rel n = ufa_\<alpha> [0..<n]"

lemma ufa_init_invar [resolve]: "ufa_invar [0..<n]" by auto2

lemma ufa_init_correct [rewrite]:
  "(x, y) \<in> uf_init_rel n \<longleftrightarrow> (x = y \<and> x < n)"
@proof @have "ufa_invar [0..<n]" @qed

abbreviation ufa_union :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "ufa_union l x y \<equiv> l[rep_of l x := rep_of l y]"

lemma ufa_union_invar [forward_arg]:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> y < length l \<Longrightarrow> l' = ufa_union l x y \<Longrightarrow> ufa_invar l'"
@proof
  @have "\<forall>i<length l'. rep_of_dom (l', i) \<and> l' ! i < length l'" @with
    @prop_induct "ufa_invar l \<and> i < length l"
  @end
@qed

lemma ufa_union_aux [rewrite]:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> y < length l \<Longrightarrow> l' = ufa_union l x y \<Longrightarrow>
   i < length l' \<Longrightarrow> rep_of l' i = (if rep_of l i = rep_of l x then rep_of l y else rep_of l i)"
@proof @prop_induct "ufa_invar l \<and> i < length l" @qed

text \<open>Correctness of union operation.\<close>
theorem ufa_union_correct [rewrite]:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> y < length l \<Longrightarrow> l' = ufa_union l x y \<Longrightarrow>
   ufa_\<alpha> l' = per_union (ufa_\<alpha> l) x y"
@proof
  @have "\<forall>a b. (a,b) \<in> ufa_\<alpha> l' \<longleftrightarrow> (a,b) \<in> per_union (ufa_\<alpha> l) x y" @with
    @case "(a,b) \<in> ufa_\<alpha> l'" @with
      @case "rep_of l a = rep_of l x"
      @case "rep_of l a = rep_of l y"
    @end
  @end
@qed

abbreviation ufa_compress :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "ufa_compress l x \<equiv> l[x := rep_of l x]"

lemma ufa_compress_invar [forward_arg]:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> l' = ufa_compress l x \<Longrightarrow> ufa_invar l'"
@proof
  @have "\<forall>i<length l'. rep_of_dom (l', i) \<and> l' ! i < length l'" @with
    @prop_induct "ufa_invar l \<and> i < length l"
  @end
@qed

lemma ufa_compress_aux [rewrite]:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> l' = ufa_compress l x \<Longrightarrow> i < length l' \<Longrightarrow>
   rep_of l' i = rep_of l i"
@proof @prop_induct "ufa_invar l \<and> i < length l" @qed

text \<open>Correctness of compress operation.\<close>
theorem ufa_compress_correct [rewrite]:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> ufa_\<alpha> (ufa_compress l x) = ufa_\<alpha> l" by auto2

setup \<open>del_prfstep_thm @{thm rep_of_iff}\<close>

end
