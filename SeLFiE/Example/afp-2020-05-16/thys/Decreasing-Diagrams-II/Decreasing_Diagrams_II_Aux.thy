(* Title:      Decreasing Diagrams II  
   Author:     Bertram Felgenhauer (2015)
   Maintainer: Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at>
   License:    LGPL or BSD

License clarification: This file is also licensed under the BSD license to facilitate reuse
and moving snippets from here to more suitable places.
*)

section \<open>Preliminaries\<close>

theory Decreasing_Diagrams_II_Aux
imports
  Well_Quasi_Orders.Multiset_Extension
  Well_Quasi_Orders.Well_Quasi_Orders
begin

subsection \<open>Trivialities\<close>

(* move to Relation.thy? *)
lemma asymI2: "(\<And>a b. (a,b) \<in> R \<Longrightarrow> (b,a) \<notin> R) \<Longrightarrow> asym R"
by (metis asymI irrefl_def)

(* move to Relation.thy? *)
abbreviation "strict_order R \<equiv> irrefl R \<and> trans R"

(* move to Relation.thy? *)
lemma order_asym: "trans R \<Longrightarrow> asym R = irrefl R"
unfolding asym.simps irrefl_def trans_def by meson

(* move to Relation.thy? *)
lemma strict_order_strict: "strict_order q \<Longrightarrow> strict (\<lambda>a b. (a, b) \<in> q\<^sup>=) = (\<lambda>a b. (a, b) \<in> q)"
unfolding trans_def irrefl_def by fast

(* move to Wellfounded.thy? *)
lemma mono_lex1: "mono (\<lambda>r. lex_prod r s)"
by (auto simp add: mono_def)

(* move to Wellfounded.thy? *)
lemma mono_lex2: "mono (lex_prod r)"
by (auto simp add: mono_def)

(* move to Wellfounded.thy? *)
lemma irrefl_lex_prod: "irrefl R \<Longrightarrow> irrefl S \<Longrightarrow> irrefl (R <*lex*> S)"
by (auto simp add: lex_prod_def irrefl_def)

lemmas converse_inward = rtrancl_converse[symmetric] converse_Un converse_UNION converse_relcomp
  converse_converse converse_Id


subsection \<open>Complete lattices and least fixed points\<close>

context complete_lattice
begin

subsubsection \<open>A chain-based induction principle\<close>

abbreviation set_chain :: "'a set \<Rightarrow> bool" where
  "set_chain C \<equiv> \<forall>x \<in> C. \<forall>y \<in> C. x \<le> y \<or> y \<le> x"
 
lemma lfp_chain_induct:
  assumes mono: "mono f"
  and step: "\<And>x. P x \<Longrightarrow> P (f x)"
  and chain: "\<And>C. set_chain C \<Longrightarrow> \<forall> x \<in> C. P x \<Longrightarrow> P (Sup C)" 
  shows "P (lfp f)"
unfolding lfp_eq_fixp[OF mono]
proof (rule fixp_induct)
  show "monotone (\<le>) (\<le>) f" using mono unfolding order_class.mono_def monotone_def .
next
  show "P (Sup {})" using chain[of "{}"] by simp
next
  show "ccpo.admissible Sup (\<le>) P"
  by (auto simp add: chain ccpo.admissible_def Complete_Partial_Order.chain_def)
qed fact


subsubsection \<open>Preservation of transitivity, asymmetry, irreflexivity by suprema\<close>

lemma trans_Sup_of_chain:
  assumes "set_chain C" and trans: "\<And>R. R \<in> C \<Longrightarrow> trans R"
  shows "trans (Sup C)"
proof (intro transI)
  fix x y z
  assume "(x,y) \<in> Sup C" and "(y,z) \<in> Sup C"
  from \<open>(x,y) \<in> Sup C\<close> obtain R where "R \<in> C" and "(x,y) \<in> R" by blast
  from \<open>(y,z) \<in> Sup C\<close> obtain S where "S \<in> C" and "(y,z) \<in> S" by blast
  from \<open>R \<in> C\<close> and \<open>S \<in> C\<close> and \<open>set_chain C\<close> have "R \<union> S = R \<or> R \<union> S = S" by blast
  with \<open>R \<in> C\<close> and \<open>S \<in> C\<close> have "R \<union> S \<in> C" by fastforce
  with \<open>(x,y) \<in> R\<close> and \<open>(y,z) \<in> S\<close> and trans[of "R \<union> S"]
  have "(x,z) \<in> R \<union> S" unfolding trans_def by blast
  with \<open>R \<union> S \<in> C\<close> show "(x,z) \<in> \<Union>C" by blast 
qed

lemma asym_Sup_of_chain:
  assumes "set_chain C" and asym: "\<And> R. R \<in> C \<Longrightarrow> asym R"
  shows "asym (Sup C)"
proof (intro asymI2 notI)
  fix a b
  assume "(a,b) \<in> Sup C" then obtain "R" where "R \<in> C" and "(a,b) \<in> R" by blast
  assume "(b,a) \<in> Sup C" then obtain "S" where "S \<in> C" and "(b,a) \<in> S" by blast
  from \<open>R \<in> C\<close> and \<open>S \<in> C\<close> and \<open>set_chain C\<close> have "R \<union> S = R \<or> R \<union> S = S" by blast
  with \<open>R \<in> C\<close> and \<open>S \<in> C\<close> have "R \<union> S \<in> C" by fastforce
  with \<open>(a,b) \<in> R\<close> and \<open>(b,a) \<in> S\<close> and asym show "False" unfolding asym.simps by blast
qed

lemma strict_order_lfp:
  assumes "mono f" and "\<And>R. strict_order R \<Longrightarrow> strict_order (f R)"
  shows "strict_order (lfp f)"
proof (intro lfp_chain_induct[of f strict_order])
  fix C :: "('b \<times> 'b) set set"
  assume "set_chain C" and "\<forall>R \<in> C. strict_order R"
  from this show "strict_order (Sup C)" by (metis asym_Sup_of_chain trans_Sup_of_chain order_asym)
qed fact+

lemma trans_lfp:
  assumes "mono f" and "\<And>R. trans R \<Longrightarrow> trans (f R)"
  shows "trans (lfp f)"
by (metis lfp_chain_induct[of f trans] assms trans_Sup_of_chain)

end (* complete_lattice *)


subsection \<open>Multiset extension\<close>

lemma mulex_iff_mult: "mulex r M N \<longleftrightarrow> (M,N) \<in> mult {(M,N) . r M N}"
by (auto simp add: mulex_on_def restrict_to_def mult_def mulex1_def tranclp_unfold)

lemma multI:
  assumes "trans r" "M = I + K" "N = I + J" "J \<noteq> {#}" "\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k,j) \<in> r"
  shows "(M,N) \<in> mult r"
using assms one_step_implies_mult by blast

lemma multE:
  assumes "trans r" and "(M,N) \<in> mult r"
  obtains I J K where "M = I + K" "N = I + J" "J \<noteq> {#}" "\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k,j) \<in> r"
using mult_implies_one_step[OF assms] by blast

lemma mult_on_union: "(M,N) \<in> mult r \<Longrightarrow> (K + M, K + N) \<in> mult r"
using mulex_on_union[of "\<lambda>x y. (x,y) \<in> r" UNIV] by (auto simp: mulex_iff_mult)

lemma mult_on_union': "(M,N) \<in> mult r \<Longrightarrow> (M + K, N + K) \<in> mult r"
using mulex_on_union'[of "\<lambda>x y. (x,y) \<in> r" UNIV] by (auto simp: mulex_iff_mult)

lemma mult_on_add_mset: "(M,N) \<in> mult r \<Longrightarrow> (add_mset k M, add_mset k N) \<in> mult r"
unfolding add_mset_add_single[of k M] add_mset_add_single[of k N] by (rule mult_on_union')

lemma mult_empty[simp]: "(M,{#}) \<notin> mult R"
by (metis mult_def not_less_empty trancl.cases)

lemma mult_singleton[simp]: "(x, y) \<in> r \<Longrightarrow> (add_mset x M, add_mset y M) \<in> mult r"
unfolding add_mset_add_single[of x M] add_mset_add_single[of y M]
apply (rule mult_on_union)
using mult1_singleton[of x y r] by (auto simp add: mult_def mult_on_union)

lemma empty_mult[simp]: "({#},N) \<in> mult R \<longleftrightarrow> N \<noteq> {#}"
using empty_mulex_on[of N UNIV "\<lambda>M N. (M,N) \<in> R"] by (auto simp add: mulex_iff_mult)

lemma trans_mult: "trans (mult R)"
unfolding mult_def by simp

lemma strict_order_mult:
  assumes "irrefl R" and "trans R"
  shows "irrefl (mult R)" and "trans (mult R)"
proof -
  show "irrefl (mult R)" unfolding irrefl_def
  proof (intro allI notI, elim multE[OF \<open>trans R\<close>])
    fix M I J K
    assume "M = I + J" "M = I + K" "J \<noteq> {#}" and *: "\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k, j) \<in> R"
    from \<open>M = I + J\<close> and \<open>M = I + K\<close> have "J = K" by simp
    have "finite (set_mset J)" by simp
    then have "set_mset J = {}" using * unfolding \<open>J = K\<close>
      by (induct rule: finite_induct)
         (simp, metis assms insert_absorb insert_iff insert_not_empty irrefl_def transD)
    then show "False" using \<open>J \<noteq> {#}\<close> by simp
  qed
qed (simp add: trans_mult)

lemma mult_of_image_mset:
  assumes "trans R" and "trans R'"
  and "\<And>x y. x \<in> set_mset N \<Longrightarrow> y \<in> set_mset M \<Longrightarrow> (x,y) \<in> R \<Longrightarrow> (f x, f y) \<in> R'"
  and "(N, M) \<in> mult R"
  shows "(image_mset f N, image_mset f M) \<in> mult R'"
proof (insert assms(4), elim multE[OF assms(1)])
  fix I J K
  assume "N = I + K" "M = I + J" "J \<noteq> {#}" "\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k, j) \<in> R"
  thus "(image_mset f N, image_mset f M) \<in> mult R'" using assms(2,3)
    by (intro multI) (auto, blast)
qed


subsection \<open>Incrementality of @{term mult1} and @{term mult}\<close>

lemma mono_mult1: "mono mult1"
unfolding mono_def mult1_def by blast

lemma mono_mult: "mono mult"
unfolding mono_def mult_def
proof (intro allI impI subsetI)
  fix R S :: "'a rel" and x
  assume "R \<subseteq> S" and "x \<in> (mult1 R)\<^sup>+"
  then show "x \<in> (mult1 S)\<^sup>+"
  using mono_mult1[unfolded mono_def] trancl_mono[of x "mult1 R" "mult1 S"] by auto
qed


subsection \<open>Well-orders and well-quasi-orders\<close>

lemma wf_iff_wfp_on:
  "wf p \<longleftrightarrow> wfp_on (\<lambda>a b. (a, b) \<in> p) UNIV"
unfolding wfp_on_iff_inductive_on wf_def inductive_on_def by force

lemma well_order_implies_wqo:
  assumes "well_order r"
  shows "wqo_on (\<lambda>a b. (a, b) \<in> r) UNIV"
proof (intro wqo_onI almost_full_onI)
  show "transp_on (\<lambda>a b. (a, b) \<in> r) UNIV" using assms
  by (auto simp only: well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def
    trans_def transp_on_def)
next
  fix f :: "nat \<Rightarrow> 'a"
  show "good (\<lambda>a b. (a, b) \<in> r) f"
  using assms unfolding well_order_on_def wf_iff_wfp_on wfp_on_def not_ex not_all de_Morgan_conj
  proof (elim conjE allE exE)
    fix x assume "linear_order r" and "f x \<notin> UNIV \<or> (f (Suc x), f x) \<notin> r - Id"
    then have "(f x, f (Suc x)) \<in> r" using \<open>linear_order r\<close>
    by (force simp: linear_order_on_def Relation.total_on_def partial_order_on_def preorder_on_def
      refl_on_def)
    then show "good (\<lambda>a b. (a, b) \<in> r) f" by (auto simp: good_def)
  qed
qed


subsection \<open>Splitting lists into prefix, element, and suffix\<close>

fun list_splits :: "'a list \<Rightarrow> ('a list \<times> 'a \<times> 'a list) list" where
  "list_splits [] = []"
| "list_splits (x # xs) = ([], x, xs) # map (\<lambda>(xs, x', xs'). (x # xs, x', xs')) (list_splits xs)"

lemma list_splits_empty[simp]:
  "list_splits xs = [] \<longleftrightarrow> xs = []"
by (cases xs) simp_all

lemma elem_list_splits_append:
  assumes "(ys, y, zs) \<in> set (list_splits xs)"
  shows "ys @ [y] @ zs = xs"
using assms by (induct xs arbitrary: ys) auto

lemma elem_list_splits_length:
  assumes "(ys, y, zs) \<in> set (list_splits xs)"
  shows "length ys < length xs" and "length zs < length xs"
using elem_list_splits_append[OF assms] by auto

lemma elem_list_splits_elem:
  assumes "(xs, y, ys) \<in> set (list_splits zs)"
  shows "y \<in> set zs"
using elem_list_splits_append[OF assms] by force

lemma list_splits_append:
  "list_splits (xs @ ys) = map (\<lambda>(xs', x', ys'). (xs', x', ys' @ ys)) (list_splits xs) @
                           map (\<lambda>(xs', x', ys'). (xs @ xs', x', ys')) (list_splits ys)"
by (induct xs) auto

lemma list_splits_rev:
  "list_splits (rev xs) = map (\<lambda>(xs, x, ys). (rev ys, x, rev xs)) (rev (list_splits xs))"
by (induct xs) (auto simp add: list_splits_append comp_def prod.case_distrib rev_map)

lemma list_splits_map:
  "list_splits (map f xs) = map (\<lambda>(xs, x, ys). (map f xs, f x, map f ys)) (list_splits xs)"
by (induct xs) auto

end (* Decreasing_Diagrams_II_Aux *)
