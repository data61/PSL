(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

section \<open>Additional material that we would have expected in Set.thy\<close>

theory SetUtils
imports
  Main

begin

subsection \<open>Equality\<close>

text \<open>An inference (introduction) rule that combines @{thm equalityI} and @{thm subsetI} to a single step\<close>
lemma equalitySubsetI: "(\<And>x . x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> (\<And>x . x \<in> B \<Longrightarrow> x \<in> A) \<Longrightarrow> A = B" 
      by blast

subsection \<open>Trivial sets\<close>

text \<open>A trivial set (i.e. singleton or empty), as in Mizar\<close>
definition trivial where "trivial x = (x \<subseteq> {the_elem x})"

text \<open>The empty set is trivial.\<close>
lemma trivial_empty: "trivial {}" 
      unfolding trivial_def by (rule empty_subsetI)

text \<open>A singleton set is trivial.\<close>
lemma trivial_singleton: "trivial {x}" 
      unfolding trivial_def by simp

text \<open>If a trivial set has a singleton subset, the latter is unique.\<close>
lemma singleton_sub_trivial_uniq:
      fixes   x X
      assumes "{x} \<subseteq> X" and "trivial X"
      shows   "x = the_elem X"
(* CL: The following takes 16 ms in Isabelle2013-1-RC1:
   by (metis assms(1) assms(2) insert_not_empty insert_subset subset_empty subset_insert trivial_def trivial_imp_no_distinct) *)
      using assms unfolding trivial_def by fast

text \<open>Any subset of a trivial set is trivial.\<close>

lemma trivial_subset: fixes X Y assumes "trivial Y" assumes "X \<subseteq> Y" 
                      shows "trivial X"
(* CL: The following takes 36 ms in Isabelle2013-1-RC1:
   by (metis assms(1) assms(2) equals0D no_distinct_imp_trivial subsetI subset_antisym subset_singletonD trivial_cases) *)
        using assms unfolding trivial_def 
        by (metis (full_types) subset_empty subset_insertI2 subset_singletonD)

text \<open>There are no two different elements in a trivial set.\<close>

lemma trivial_imp_no_distinct:
  assumes triv: "trivial X" and x: "x \<in> X" and y: "y \<in> X"
  shows   "x = y"
(* CL: The following takes 17 ms in Isabelle2013-1-RC1: *)
  using assms by (metis empty_subsetI insert_subset singleton_sub_trivial_uniq) 

subsection \<open>The image of a set under a function\<close>

text \<open>an equivalent notation for the image of a set, using set comprehension\<close>
lemma image_Collect_mem: "{ f x | x . x \<in> S } = f ` S" 
      by auto

subsection \<open>Big Union\<close>

text \<open>An element is in the union of a family of sets if it is in one of the family's member sets.\<close>

lemma Union_member: "(\<exists> S \<in> F . x \<in> S) \<longleftrightarrow> x \<in> \<Union> F" 
      by blast

subsection \<open>Miscellaneous\<close>

lemma trivial_subset_non_empty: assumes "trivial t" "t \<inter> X \<noteq> {}" 
            shows   "t \<subseteq> X" 
      using trivial_def assms in_mono by fast

lemma trivial_implies_finite: assumes "trivial X" 
            shows   "finite X" 
      using assms by (metis finite.simps subset_singletonD trivial_def)
(* finite.simps trivial_cases by metis *)

lemma lm01: assumes "trivial (A \<times> B)" 
              shows   "(finite (A\<times>B) & card A * (card B) \<le> 1)" 
      using trivial_def assms One_nat_def card_cartesian_product card_empty card_insert_disjoint
            empty_iff finite.emptyI le0 trivial_implies_finite order_refl subset_singletonD by (metis(no_types))

lemma lm02: assumes "finite X" 
            shows   "trivial X=(card X \<le> 1)" 
      using assms One_nat_def card_empty card_insert_if card_mono card_seteq empty_iff 
            empty_subsetI finite.cases finite.emptyI finite_insert insert_mono 
            trivial_def trivial_singleton
      by (metis(no_types))

lemma lm03: shows "trivial {x}" 
      by (metis order_refl the_elem_eq trivial_def)

lemma lm04: assumes "trivial X" "{x} \<subseteq> X" 
            shows   "{x} = X" 
      using singleton_sub_trivial_uniq assms by (metis subset_antisym trivial_def)

lemma lm05: assumes "\<not> trivial X" "trivial T" 
            shows   "X - T  \<noteq>  {}"
      using assms by (metis Diff_iff empty_iff subsetI trivial_subset)

lemma lm06: assumes "(finite (A \<times> B)  &  card A * (card B) \<le> 1)" 
              shows   "trivial (A \<times> B)" 
      unfolding trivial_def using trivial_def assms by (metis card_cartesian_product lm02)

lemma lm07: "trivial (A \<times> B) = (finite (A \<times> B) & card A * (card B) \<le> 1)" 
      using lm01 lm06 by blast

lemma trivial_empty_or_singleton: "trivial X = (X = {} \<or> X = {the_elem X})" 
      by (metis subset_singletonD trivial_def trivial_empty trivial_singleton)

lemma trivial_cartesian: assumes "trivial X" "trivial Y" 
            shows   "trivial (X \<times> Y)"
      using assms lm07 One_nat_def Sigma_empty1 Sigma_empty2 card_empty card_insert_if
            finite_SigmaI trivial_implies_finite nat_1_eq_mult_iff order_refl subset_singletonD trivial_def trivial_empty
      by (metis (full_types))

lemma trivial_same: "trivial X = (\<forall>x1 \<in> X. \<forall>x2 \<in> X. x1 = x2)" 
      using trivial_def trivial_imp_no_distinct ex_in_conv insertCI subsetI subset_singletonD
            trivial_singleton 
      by (metis (no_types, hide_lams))

lemma lm08: assumes "(Pow X \<subseteq> {{},X})" 
              shows  "trivial X" 
      unfolding trivial_same using assms by auto

lemma lm09: assumes "trivial X" 
              shows "(Pow X \<subseteq> {{},X})" 
      using assms trivial_same by fast

lemma lm10: "trivial X = (Pow X \<subseteq> {{},X})" 
      using lm08 lm09 by metis

lemma lm11: "({x} \<times> UNIV) \<inter> P = {x} \<times> (P `` {x})" 
      by fast

lemma lm12: "(x,y) \<in> P = (y \<in> P``{x})" 
      by simp

lemma lm13: assumes "inj_on f A" "inj_on f B" 
             shows   "inj_on f (A \<union> B)  =  (f`(A-B) \<inter> (f`(B-A)) = {})"
      using assms inj_on_Un by (metis)

lemma injection_union: assumes "inj_on f A" "inj_on f B" "(f`A) \<inter> (f`B) = {}" 
              shows "inj_on f (A \<union> B)" 
      using assms lm13 by fast

lemma lm14: "(Pow X = {X}) = (X={})" 
      by auto

end

