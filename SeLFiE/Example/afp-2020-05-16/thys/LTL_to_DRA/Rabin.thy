(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>(Generalized) Rabin Automata\<close>

theory Rabin
  imports Main DTS
begin

type_synonym ('a, 'b) rabin_pair = "(('a, 'b) transition set \<times> ('a, 'b) transition set)"
type_synonym ('a, 'b) generalized_rabin_pair = "(('a, 'b) transition set \<times> ('a, 'b) transition set set)"

type_synonym ('a, 'b) rabin_condition = "('a, 'b) rabin_pair set"
type_synonym ('a, 'b) generalized_rabin_condition = "('a, 'b) generalized_rabin_pair set"

type_synonym ('a, 'b) rabin_automaton = "('a, 'b) DTS \<times> 'a \<times> ('a, 'b) rabin_condition"
type_synonym ('a, 'b) generalized_rabin_automaton = "('a, 'b) DTS \<times> 'a \<times> ('a, 'b) generalized_rabin_condition"

definition accepting_pair\<^sub>R :: "('a, 'b) DTS \<Rightarrow> 'a \<Rightarrow> ('a, 'b) rabin_pair \<Rightarrow> 'b word \<Rightarrow> bool"
where
  "accepting_pair\<^sub>R \<delta> q\<^sub>0 P w \<equiv> limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> fst P = {} \<and> limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> snd P \<noteq> {}"

definition accept\<^sub>R :: "('a, 'b) rabin_automaton \<Rightarrow> 'b word \<Rightarrow> bool"
where 
  "accept\<^sub>R R w \<equiv> (\<exists>P \<in> (snd (snd R)). accepting_pair\<^sub>R (fst R) (fst (snd R)) P w)"

definition accepting_pair\<^sub>G\<^sub>R :: "('a, 'b) DTS \<Rightarrow> 'a \<Rightarrow> ('a, 'b) generalized_rabin_pair \<Rightarrow> 'b word \<Rightarrow> bool"
where
  "accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 P w \<equiv> limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> fst P = {} \<and> (\<forall>I \<in> snd P. limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> I \<noteq> {})"

definition accept\<^sub>G\<^sub>R :: "('a, 'b) generalized_rabin_automaton \<Rightarrow> 'b word \<Rightarrow> bool"
where 
  "accept\<^sub>G\<^sub>R R w \<equiv> (\<exists>(Fin, Inf) \<in> (snd (snd R)). accepting_pair\<^sub>G\<^sub>R (fst R) (fst (snd R)) (Fin, Inf) w)"

declare accepting_pair\<^sub>R_def[simp]
declare accepting_pair\<^sub>G\<^sub>R_def[simp]

lemma accepting_pair\<^sub>R_simp[simp]:
  "accepting_pair\<^sub>R \<delta> q\<^sub>0 (F,I) w \<equiv> limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> F = {} \<and> limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> I \<noteq> {}"
  by simp

lemma accepting_pair\<^sub>G\<^sub>R_simp[simp]:
  "accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (F, \<I>) w \<equiv> limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> F = {} \<and> (\<forall>I \<in> \<I>. limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> I \<noteq> {})"
  by simp

lemma accept\<^sub>R_simp[simp]:
  "accept\<^sub>R (\<delta>, q\<^sub>0, \<alpha>) w = (\<exists>(Fin, Inf) \<in> \<alpha>. limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> Fin = {} \<and> limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> Inf \<noteq> {})"
  by (unfold accept\<^sub>R_def accepting_pair\<^sub>R_def case_prod_unfold fst_conv snd_conv; rule)

lemma accept\<^sub>G\<^sub>R_simp[simp]: 
  "accept\<^sub>G\<^sub>R (\<delta>, q\<^sub>0, \<alpha>) w \<longleftrightarrow> (\<exists>(Fin, Inf) \<in> \<alpha>. limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> Fin = {} \<and> (\<forall>I \<in> Inf. limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> I \<noteq> {}))"
  by (unfold accept\<^sub>G\<^sub>R_def accepting_pair\<^sub>G\<^sub>R_def case_prod_unfold fst_conv snd_conv; rule)

lemma accept\<^sub>G\<^sub>R_simp2: 
  "accept\<^sub>G\<^sub>R (\<delta>, q\<^sub>0, \<alpha>) w \<longleftrightarrow> (\<exists>P \<in> \<alpha>. accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 P w)"
  by (unfold accept\<^sub>G\<^sub>R_def accepting_pair\<^sub>G\<^sub>R_def case_prod_unfold fst_conv snd_conv; rule)

type_synonym ('a, 'b) LTS = "('a, 'b) transition set"

definition LTS_is_inf_run :: "('q,'a) LTS \<Rightarrow> 'a word \<Rightarrow> 'q word \<Rightarrow> bool" where
  "LTS_is_inf_run \<Delta> w r \<longleftrightarrow> (\<forall>i. (r i, w i, r (Suc i)) \<in> \<Delta>)"

fun accept\<^sub>R_LTS :: "(('a, 'b) LTS \<times> 'a \<times> ('a, 'b) rabin_condition) \<Rightarrow> 'b word \<Rightarrow> bool"
where 
  "accept\<^sub>R_LTS (\<delta>, q\<^sub>0, \<alpha>) w \<longleftrightarrow> (\<exists>(Fin, Inf) \<in> \<alpha>. \<exists>r. 
      LTS_is_inf_run \<delta> w r \<and> r 0 = q\<^sub>0 
    \<and> limit (\<lambda>i. (r i, w i, r (Suc i))) \<inter> Fin = {} 
    \<and> limit (\<lambda>i. (r i, w i, r (Suc i))) \<inter> Inf \<noteq> {})"

definition accepting_pair\<^sub>G\<^sub>R_LTS :: "('a, 'b) LTS \<Rightarrow> 'a \<Rightarrow> ('a, 'b) generalized_rabin_pair \<Rightarrow> 'b word \<Rightarrow> bool"
where
  "accepting_pair\<^sub>G\<^sub>R_LTS \<delta> q\<^sub>0 P w \<equiv> \<exists>r. LTS_is_inf_run \<delta> w r \<and> r 0 = q\<^sub>0 
    \<and> limit (\<lambda>i. (r i, w i, r (Suc i))) \<inter> fst P = {} 
    \<and> (\<forall>I \<in> snd P. limit (\<lambda>i. (r i, w i, r (Suc i))) \<inter> I \<noteq> {})"

fun accept\<^sub>G\<^sub>R_LTS :: "(('a, 'b) LTS \<times> 'a \<times> ('a, 'b) generalized_rabin_condition) \<Rightarrow> 'b word \<Rightarrow> bool"
where 
  "accept\<^sub>G\<^sub>R_LTS (\<delta>, q\<^sub>0, \<alpha>) w = (\<exists>(Fin, Inf) \<in> \<alpha>. accepting_pair\<^sub>G\<^sub>R_LTS \<delta> q\<^sub>0 (Fin, Inf) w)"

lemma accept\<^sub>G\<^sub>R_LTS_E:
  assumes "accept\<^sub>G\<^sub>R_LTS R w"
  obtains F I where "(F, I) \<in> snd (snd R)"
   and "accepting_pair\<^sub>G\<^sub>R_LTS (fst R) (fst (snd R)) (F, I) w"
proof -
  obtain \<delta> q\<^sub>0 \<alpha> where "R = (\<delta>, q\<^sub>0, \<alpha>)"
    using prod_cases3 by blast
  show "(\<And>F I. (F, I) \<in> snd (snd R) \<Longrightarrow> accepting_pair\<^sub>G\<^sub>R_LTS (fst R) (fst (snd R)) (F, I) w \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    using assms unfolding \<open>R = (\<delta>, q\<^sub>0, \<alpha>)\<close> by auto
qed

lemma accept\<^sub>G\<^sub>R_LTS_I:
  "accepting_pair\<^sub>G\<^sub>R_LTS \<delta> q\<^sub>0 (F, \<I>) w \<Longrightarrow> (F, \<I>) \<in> \<alpha> \<Longrightarrow> accept\<^sub>G\<^sub>R_LTS (\<delta>, q\<^sub>0, \<alpha>) w"
  by auto

lemma accept\<^sub>G\<^sub>R_I:
  "accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (F, \<I>) w \<Longrightarrow> (F, \<I>) \<in> \<alpha> \<Longrightarrow> accept\<^sub>G\<^sub>R (\<delta>, q\<^sub>0, \<alpha>) w"
  by auto

lemma transfer_accept:
  "accepting_pair\<^sub>R \<delta> q\<^sub>0 (F, I) w \<longleftrightarrow> accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (F, {I}) w"
  "accept\<^sub>R (\<delta>, q\<^sub>0, \<alpha>) w \<longleftrightarrow> accept\<^sub>G\<^sub>R (\<delta>, q\<^sub>0, (\<lambda>(F, I). (F, {I})) ` \<alpha>) w"
  by (simp add: case_prod_unfold)+

subsection \<open>Restriction Lemmas\<close>

lemma accepting_pair\<^sub>G\<^sub>R_restrict:
  assumes "range w \<subseteq> \<Sigma>"
  shows "accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (F, \<I>) w = accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (F \<inter> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0, (\<lambda>I. I \<inter> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) ` \<I>) w"
proof -
  have "limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> F = {} \<longleftrightarrow> limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> (F \<inter> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) = {}"
    using assms[THEN limit_subseteq_reach(2), of \<delta> q\<^sub>0] by auto
  moreover
  have "(\<forall>I\<in>\<I>. limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> I \<noteq> {}) = ((\<forall>I\<in>{y. \<exists>x\<in>\<I>. y = x \<inter> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0}. limit (run\<^sub>t \<delta> q\<^sub>0 w) \<inter> I \<noteq> {}))"
     using assms[THEN limit_subseteq_reach(2), of \<delta> q\<^sub>0] by auto
  ultimately
  show ?thesis
    unfolding accepting_pair\<^sub>G\<^sub>R_simp image_def by meson
qed

lemma accept\<^sub>G\<^sub>R_restrict:
  assumes "range w \<subseteq> \<Sigma>"
  shows "accept\<^sub>G\<^sub>R (\<delta>, q\<^sub>0, {(f x, g x) | x. P x}) w = accept\<^sub>G\<^sub>R (\<delta>, q\<^sub>0, {(f x \<inter> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0, (\<lambda>I. I \<inter> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) ` g x) | x. P x}) w"
  apply (simp only: accept\<^sub>G\<^sub>R_simp)  
  apply (subst accepting_pair\<^sub>G\<^sub>R_restrict[OF assms, simplified]) 
  apply simp
  apply standard
  apply (metis (no_types, lifting) imageE) 
  apply fastforce
  done

lemma accepting_pair\<^sub>R_restrict:
  assumes "range w \<subseteq> \<Sigma>"
  shows "accepting_pair\<^sub>R \<delta> q\<^sub>0 (F, I) w = accepting_pair\<^sub>R \<delta> q\<^sub>0 (F \<inter> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0, I \<inter> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) w"
  by (simp only: transfer_accept; subst accepting_pair\<^sub>G\<^sub>R_restrict[OF assms]; simp)

lemma accept\<^sub>R_restrict:
  assumes "range w \<subseteq> \<Sigma>"
  shows "accept\<^sub>R (\<delta>, q\<^sub>0, {(f x, g x) | x. P x}) w = accept\<^sub>R (\<delta>, q\<^sub>0, {(f x \<inter> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0, g x \<inter> reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) | x. P x}) w"
  by (simp only: accept\<^sub>R_simp; subst accepting_pair\<^sub>R_restrict[OF assms, simplified]; auto)

subsection \<open>Abstraction Lemmas\<close>

lemma accepting_pair\<^sub>G\<^sub>R_abstract:
  assumes "finite (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0)" 
      and "finite (reach\<^sub>t \<Sigma> \<delta>' q\<^sub>0')"
  assumes "range w \<subseteq> \<Sigma>"
  assumes "run\<^sub>t \<delta> q\<^sub>0 w = f o (run\<^sub>t \<delta>' q\<^sub>0' w)"
  assumes "\<And>t. t \<in> reach\<^sub>t \<Sigma> \<delta>' q\<^sub>0' \<Longrightarrow> f t \<in> F \<longleftrightarrow> t \<in> F'"
  assumes "\<And>t i. i \<in> \<I> \<Longrightarrow> t \<in> reach\<^sub>t \<Sigma> \<delta>' q\<^sub>0' \<Longrightarrow> f t \<in> I i \<longleftrightarrow> t \<in> I' i"
  shows "accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (F, {I i | i. i \<in> \<I>}) w \<longleftrightarrow> accepting_pair\<^sub>G\<^sub>R \<delta>' q\<^sub>0' (F', {I' i | i. i \<in> \<I>}) w"
proof -
  have "finite (range (run\<^sub>t \<delta> q\<^sub>0 w))" (is "_ (range ?r)") 
    and "finite (range (run\<^sub>t \<delta>' q\<^sub>0' w))" (is "_ (range ?r')")
    using assms(1,2,3) run_subseteq_reach(2) by (metis finite_subset)+
  then obtain k where 1: "limit ?r = range (suffix k ?r)"
    and 2: "limit ?r' = range (suffix k ?r')"
    using common_range_limit by blast
  have X: "limit (run\<^sub>t \<delta> q\<^sub>0 w) = f ` limit (run\<^sub>t \<delta>' q\<^sub>0' w)"
    unfolding 1 2 suffix_def by (auto simp add: assms(4))
  have 3: "(limit ?r \<inter> F = {}) \<longleftrightarrow> (limit ?r' \<inter> F' = {})"
    and 4: "(\<forall>i \<in> \<I>. limit ?r \<inter> I i \<noteq> {}) \<longleftrightarrow> (\<forall>i \<in> \<I>. limit ?r' \<inter> I' i \<noteq> {})"
    using assms(5,6) limit_subseteq_reach(2)[OF assms(3)] by (unfold X; fastforce)+
  thus ?thesis
    unfolding accepting_pair\<^sub>G\<^sub>R_simp by blast
qed

lemma accepting_pair\<^sub>R_abstract:
  assumes "finite (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0)" 
      and "finite (reach\<^sub>t \<Sigma> \<delta>' q\<^sub>0')"
  assumes "range w \<subseteq> \<Sigma>"
  assumes "run\<^sub>t \<delta> q\<^sub>0 w  = f o (run\<^sub>t \<delta>' q\<^sub>0' w)"
  assumes "\<And>t. t \<in> reach\<^sub>t \<Sigma> \<delta>' q\<^sub>0' \<Longrightarrow> f t \<in> F \<longleftrightarrow> t \<in> F'"
  assumes "\<And>t. t \<in> reach\<^sub>t \<Sigma> \<delta>' q\<^sub>0' \<Longrightarrow> f t \<in> I \<longleftrightarrow> t \<in> I'"
  shows "accepting_pair\<^sub>R \<delta> q\<^sub>0 (F, I) w \<longleftrightarrow> accepting_pair\<^sub>R \<delta>' q\<^sub>0' (F', I') w"
  using accepting_pair\<^sub>G\<^sub>R_abstract[OF assms(1-5), of UNIV "\<lambda>_. I" "\<lambda>_. I'"] assms(6) by simp

subsection \<open>LTS Lemmas\<close>

lemma accepting_pair\<^sub>G\<^sub>R_LTS:
  assumes "range w \<subseteq> \<Sigma>"
  shows "accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (F, \<I>) w \<longleftrightarrow> accepting_pair\<^sub>G\<^sub>R_LTS (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) q\<^sub>0 (F, \<I>) w" 
  (is "?lhs \<longleftrightarrow> ?rhs")
proof 
  {
    assume ?lhs
    moreover
    have "LTS_is_inf_run (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) w (run \<delta> q\<^sub>0 w)"
      unfolding LTS_is_inf_run_def reach\<^sub>t_def using assms(1) by auto
    moreover
    have "run \<delta> q\<^sub>0 w 0 = q\<^sub>0"
      by simp
    ultimately
    show ?rhs
      unfolding accept\<^sub>G\<^sub>R_simp accept\<^sub>G\<^sub>R_LTS.simps accepting_pair\<^sub>G\<^sub>R_simp run\<^sub>t.simps limit_def accepting_pair\<^sub>G\<^sub>R_LTS_def snd_conv fst_conv by blast
  }
  
  {
    assume ?rhs
    then obtain r where "LTS_is_inf_run (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) w r"
      and "r 0 = q\<^sub>0"
      and "limit (\<lambda>i. (r i, w i, r (Suc i))) \<inter> F = {}"
      and "\<And>I. I \<in> \<I> \<Longrightarrow> limit (\<lambda>i. (r i, w i, r (Suc i))) \<inter> I \<noteq> {}"
      unfolding accepting_pair\<^sub>G\<^sub>R_LTS_def by auto
    moreover
    {
      fix i
      from \<open>r 0 = q\<^sub>0\<close> \<open>LTS_is_inf_run (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0) w r\<close> have "r i = run \<delta> q\<^sub>0 w i"
        by (induction i; simp_all add: LTS_is_inf_run_def reach\<^sub>t_def) metis
    }
    hence "r = run \<delta> q\<^sub>0 w"
      by blast
    hence "(\<lambda>i. (r i, w i, r (Suc i))) = run\<^sub>t \<delta> q\<^sub>0 w"
      by auto
    ultimately
    show ?lhs
      by auto
  }
qed

lemma accept\<^sub>G\<^sub>R_LTS:
  assumes "range w \<subseteq> \<Sigma>"
  shows "accept\<^sub>G\<^sub>R (\<delta>, q\<^sub>0, \<alpha>) w \<longleftrightarrow> accept\<^sub>G\<^sub>R_LTS (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0, q\<^sub>0, \<alpha>) w" 
  unfolding accept\<^sub>G\<^sub>R_def fst_conv snd_conv accepting_pair\<^sub>G\<^sub>R_LTS[OF assms] by simp

lemma accept\<^sub>R_LTS:
  assumes "range w \<subseteq> \<Sigma>"
  shows "accept\<^sub>R (\<delta>, q\<^sub>0, \<alpha>) w \<longleftrightarrow> accept\<^sub>R_LTS (reach\<^sub>t \<Sigma> \<delta> q\<^sub>0, q\<^sub>0, \<alpha>) w"
  unfolding transfer_accept accept\<^sub>G\<^sub>R_LTS.simps accept\<^sub>R_LTS.simps accept\<^sub>G\<^sub>R_LTS[OF assms] case_prod_unfold accepting_pair\<^sub>G\<^sub>R_LTS_def by simp

subsection \<open>Combination Lemmas\<close>

lemma combine_rabin_pairs: 
  "(\<And>x. x \<in> I \<Longrightarrow> accepting_pair\<^sub>R \<delta> q\<^sub>0 (f x, g x) w) \<Longrightarrow> accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (\<Union>{f x | x. x \<in> I}, {g x | x. x \<in> I}) w" 
  by auto

lemma combine_rabin_pairs_UNIV: 
  "accepting_pair\<^sub>R \<delta> q\<^sub>0 (fin, UNIV) w \<Longrightarrow> accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (fin', inf') w \<Longrightarrow> accepting_pair\<^sub>G\<^sub>R \<delta> q\<^sub>0 (fin \<union> fin', inf') w"
  by auto

end
