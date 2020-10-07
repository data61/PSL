(*  Title:       Formalization of Decreasing Diagrams
    Author:      Harald Zankl  <Harald.Zankl at uibk.ac.at>, 2012
    Maintainer:  Harald Zankl  <Harald.Zankl at uibk.ac.at>, 2013
*)

(*
Copyright 2012 Harald Zankl

This formalization is free software: you can redistribute it and/or modify it under
the terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later version.

This formalization is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with the formalization. If not, see <http://www.gnu.org/licenses/>.
*)

section "Decreasing Diagrams"


theory Decreasing_Diagrams imports "HOL-Library.Multiset" "Abstract-Rewriting.Abstract_Rewriting" begin

subsection  \<open>Valley Version\<close>

text \<open>This section follows~\cite{vO94}.\<close>

subsubsection \<open>Appendix\<close>

text \<open>interaction of multisets with sets\<close>
definition diff :: "'a multiset \<Rightarrow> 'a set \<Rightarrow> 'a multiset"
 where "diff M S = filter_mset (\<lambda>x. x \<notin> S) M"

definition intersect :: "'a multiset \<Rightarrow> 'a set \<Rightarrow> 'a multiset"
 where "intersect M S = filter_mset (\<lambda>x. x \<in> S) M"

notation
 diff      (infixl "-s" 800) and
 intersect (infixl "\<inter>s" 800)

lemma count_diff [simp]:
  "count (M -s A) a = count M a * of_bool (a \<notin> A)"
  by (simp add: diff_def)

lemma set_mset_diff [simp]:
  "set_mset (M -s A) = set_mset M - A"
  by (auto simp add: diff_def)

lemma diff_eq_singleton_imp:
  "M -s A = {#a#} \<Longrightarrow> a \<in> (set_mset M - A)"
  unfolding diff_def filter_mset_eq_conv by auto

lemma count_intersect [simp]:
  "count (M \<inter>s A) a = count M a * of_bool (a \<in> A)"
  by (simp add: intersect_def)

lemma set_mset_intersect [simp]:
  "set_mset (M \<inter>s A) = set_mset M \<inter> A"
  by (auto simp add: intersect_def)

lemma diff_from_empty: "{#}-s S = {#}" unfolding diff_def by auto

lemma diff_empty: "M -s {} = M" unfolding diff_def by (rule multiset_eqI) simp

lemma submultiset_implies_subset: assumes "M \<subseteq># N" shows "set_mset M \<subseteq> set_mset N"
 using assms mset_subset_eqD by auto

lemma subset_implies_remove_empty: assumes "set_mset M \<subseteq> S" shows "M -s S = {#}"
 unfolding diff_def using assms by (induct M) auto

lemma remove_empty_implies_subset: assumes "M -s S = {#}" shows "set_mset M \<subseteq> S" proof
 fix x assume A: "x \<in> set_mset M"
 have "x \<notin> set_mset (M -s S)" using assms by auto
 thus "x \<in> S" using A unfolding diff_def by auto
qed

lemma lemmaA_3_8:  "(M + N) -s S = (M -s S) + (N -s S)" unfolding diff_def by (rule multiset_eqI) simp
lemma lemmaA_3_9:  "(M -s S) -s T = M -s (S \<union> T)" unfolding diff_def by (rule multiset_eqI) simp
lemma lemmaA_3_10: "M = (M \<inter>s S) + (M -s S)" unfolding diff_def intersect_def by auto
lemma lemmaA_3_11: "(M -s T) \<inter>s S = (M \<inter>s S) -s T" unfolding diff_def intersect_def by (rule multiset_eqI) simp

subsubsection \<open>Multisets\<close>
text \<open>Definition 2.5(1)\<close>
definition ds :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set"
 where "ds r S = {y . \<exists>x \<in> S. (y,x) \<in> r}"

definition dm :: "'a rel \<Rightarrow> 'a multiset \<Rightarrow> 'a set"
 where "dm r M = ds r (set_mset M)"

definition dl :: "'a rel \<Rightarrow> 'a list \<Rightarrow> 'a set"
 where "dl r \<sigma> = ds r (set \<sigma>)"

notation
 ds (infixl "\<down>s" 900) and
 dm (infixl "\<down>m" 900) and
 dl (infixl "\<down>l" 900)

text \<open>missing but useful\<close>
lemma ds_ds_subseteq_ds: assumes t: "trans r" shows "ds r (ds r S) \<subseteq> ds r S" proof
 fix x assume A: "x \<in> ds r (ds r S)" show "x \<in> ds r S" proof -
  from A obtain y z where "(x,y) \<in> r" and "(y,z) \<in> r" and mem: "z \<in> S" unfolding ds_def by auto
  thus ?thesis using mem t trans_def unfolding ds_def by fast
 qed
qed

text \<open>from PhD thesis of van Oostrom\<close>
lemma ds_monotone: assumes "S \<subseteq> T" shows "ds r S \<subseteq> ds r T" using assms unfolding ds_def by auto

lemma subset_imp_ds_subset: assumes "trans r" and "S \<subseteq> ds r T" shows "ds r S \<subseteq> ds r T"
 using assms ds_monotone ds_ds_subseteq_ds by blast

text \<open>Definition 2.5(2)\<close>

text \<open>strict order (mult) is used from Multiset.thy\<close>
definition mult_eq :: "'a rel \<Rightarrow> 'a multiset rel" where
  "mult_eq r = (mult1 r)\<^sup>*"

definition mul :: "'a rel \<Rightarrow> 'a multiset rel" where
  "mul r = {(M,N).\<exists>I J K. M = I + K \<and> N = I + J \<and> set_mset K \<subseteq> dm r J \<and> J \<noteq> {#}}"

definition mul_eq :: "'a rel \<Rightarrow> 'a multiset rel" where
  "mul_eq r = {(M,N).\<exists>I J K. M = I + K \<and> N = I + J \<and> set_mset K \<subseteq> dm r J}"

lemma in_mul_eqI:
  assumes "M = I + K" "N = I + J" "set_mset K \<subseteq> r \<down>m J"
  shows "(M, N) \<in> mul_eq r"
  using assms by (auto simp add: mul_eq_def)

lemma downset_intro:
assumes "\<forall>k\<in>set_mset K.\<exists>j\<in>set_mset J.(k,j)\<in>r" shows "set_mset K \<subseteq> dm r J" proof
 fix x assume "x\<in>set_mset K" thus "x \<in> dm r J" using assms unfolding dm_def ds_def by fast
qed

lemma downset_elim:
assumes "set_mset K \<subseteq> dm r J" shows "\<forall>k\<in>set_mset K.\<exists>j\<in>set_mset J.(k,j)\<in>r" proof
 fix k assume "k\<in> set_mset K" thus "\<exists>j\<in>set_mset J.(k,j)\<in> r" using assms unfolding dm_def ds_def by fast
qed

text \<open>to closure-free representation\<close>
lemma mult_eq_implies_one_or_zero_step:
assumes "trans r" and "(M,N) \<in> mult_eq r" shows "\<exists>I J K. N = I + J \<and> M = I + K \<and> set_mset K \<subseteq> dm r J"
proof (cases "(M,N) \<in> mult r")
  case True thus ?thesis using mult_implies_one_step[OF assms(1)] downset_intro by blast
 next
  case False hence A: "M = N" using assms rtrancl_eq_or_trancl unfolding mult_eq_def mult_def by metis
  hence "N = N + {#} \<and> M = M + {#} \<and> set_mset {#} \<subseteq> dm r{#}" by auto
  thus ?thesis unfolding A by fast
qed

text \<open>from closure-free representation\<close>
lemma one_step_implies_mult_eq: assumes "trans r" and "set_mset K \<subseteq> dm r J" shows "(I+K,I+J)\<in>mult_eq r"
proof (cases "set_mset J = {}")
 case True hence "set_mset K = {}" using assms downset_elim by (metis all_not_in_conv emptyE)
 thus ?thesis using True unfolding mult_eq_def by auto
next
 case False hence h:"J \<noteq> {#}" using set_mset_eq_empty_iff by auto
  hence "(I+K,I+J)\<in> mult r" using set_mset_eq_empty_iff assms one_step_implies_mult downset_elim
    by auto blast
  thus ?thesis unfolding mult_eq_def mult_def by auto
qed

lemma mult_is_mul: assumes "trans r" shows "mult r = mul r" proof
 show "mult r \<subseteq> mul r" proof
  fix N M assume A: "(N,M) \<in> mult r" show "(N,M) \<in> mul r" proof -
   obtain I J K where "M = I + J" and "N = I + K" and "J \<noteq> {#}" and "set_mset K \<subseteq> dm r J"
    using mult_implies_one_step[OF assms A] downset_intro by metis
   thus ?thesis unfolding mul_def by auto
  qed
 qed
 next
 show "mul r \<subseteq> mult r" proof
  fix N M assume A: "(N,M) \<in> mul r" show "(N,M) \<in> mult r" proof -
   obtain I J K where "M = I + J" and "N = I + K" and "J \<noteq> {#}" and "set_mset K \<subseteq> dm r J"
    using A unfolding mul_def by auto
   thus ?thesis using one_step_implies_mult assms downset_elim by metis
  qed
  qed
qed

lemma mult_eq_is_mul_eq: assumes "trans r" shows "mult_eq r = mul_eq r" proof
 show "mult_eq r \<subseteq> mul_eq r" proof
  fix N M assume A: "(N,M) \<in> mult_eq r" show "(N,M) \<in> mul_eq r" proof (cases "(N,M) \<in> mult r")
   case True thus ?thesis unfolding mult_is_mul[OF assms] mul_def mul_eq_def by auto
  next
   case False hence eq: "N = M" using A rtranclD unfolding mult_def mult_eq_def by metis
   hence "M = M + {#} \<and> N = N + {#} \<and> set_mset {#} \<subseteq> dm r {#}" by auto
   thus ?thesis unfolding eq unfolding mul_eq_def by fast
  qed
 qed
 show "mul_eq r \<subseteq> mult_eq r" using one_step_implies_mult_eq[OF assms] unfolding mul_eq_def by auto
qed

lemma "mul_eq r = (mul r)\<^sup>=" proof
 show "mul_eq r \<subseteq> (mul r)\<^sup>=" proof
  fix M N assume A:"(M,N) \<in> mul_eq r" show "(M,N) \<in> (mul r)\<^sup>=" proof -
   from A obtain I J K where 1: "M = I + K" and 2: "N = I + J" and 3: "set_mset K \<subseteq> dm r J" unfolding mul_eq_def by auto
   show ?thesis proof (cases "J = {#}")
    case True hence "K = {#}" using 3 unfolding dm_def ds_def by auto
    hence "M = N" using True 1 2 by auto
    thus ?thesis by auto
   next
    case False thus ?thesis using 1 2 3 unfolding mul_def mul_eq_def by auto
   qed
  qed
 qed
 show "mul_eq r \<supseteq> (mul r)\<^sup>=" proof
  fix M N assume A:"(M,N) \<in> (mul r)\<^sup>=" show "(M,N) \<in> mul_eq r"
   proof (cases "M = N")
    case True hence "M = M + {#}" and "N = M + {#}" and "set_mset {#} \<subseteq> dm r {#}" by auto
    thus ?thesis unfolding mul_eq_def by fast
   next
    case False hence "(M,N) \<in> mul r" using A by auto
    thus ?thesis unfolding mul_def mul_eq_def by auto
  qed
 qed
qed

text\<open>useful properties on multisets\<close>
lemma mul_eq_reflexive: "(M,M) \<in> mul_eq r" proof -
 have "M = M + {#}" and "set_mset {#} \<subseteq> dm r {#}" by auto
 thus ?thesis unfolding mul_eq_def by fast
qed

lemma mul_eq_trans: assumes "trans r" and "(M,N) \<in> mul_eq r" and "(N,P) \<in> mul_eq r" shows "(M,P) \<in> mul_eq r"
 using assms unfolding mult_eq_is_mul_eq[symmetric,OF assms(1)] mult_eq_def
by auto

lemma mul_eq_singleton: assumes "(M, {#\<alpha>#}) \<in> mul_eq r" shows "M = {#\<alpha>#} \<or> set_mset M \<subseteq> dm r {#\<alpha>#}" proof -
 from assms obtain I J K where 1:"M = I + K" and 2:"{#\<alpha>#} = I + J" and 3:"set_mset K \<subseteq> dm r J" unfolding mul_eq_def by auto
 thus ?thesis proof (cases "I = {#}")
  case True hence "J = {#\<alpha>#}" using 2 by auto
  thus ?thesis using 1 3 True by auto
 next
  case False hence i: "I = {#\<alpha>#}" using 2 union_is_single by metis
  hence "J = {#}" using 2 union_is_single by metis
  thus ?thesis using 1 i 3 unfolding dm_def ds_def by auto
 qed
qed

lemma mul_and_mul_eq_imp_mul: assumes "trans r" and "(M,N) \<in> mul r" and "(N,P) \<in> mul_eq r" shows "(M,P) \<in> mul r"
 using assms unfolding mult_is_mul[symmetric,OF assms(1)] mult_eq_is_mul_eq[symmetric,OF assms(1)] mult_def mult_eq_def by auto

lemma mul_eq_and_mul_imp_mul: assumes "trans r" and "(M,N) \<in> mul_eq r" and "(N,P) \<in> mul r" shows "(M,P) \<in> mul r"
 using assms unfolding mult_is_mul[symmetric,OF assms(1)] mult_eq_is_mul_eq[symmetric,OF assms(1)] mult_def mult_eq_def by auto

lemma wf_mul: assumes "trans r" and "wf r" shows "wf (mul r)"
 unfolding mult_is_mul[symmetric,OF assms(1)] using wf_mult[OF assms(2)] by auto

lemma remove_is_empty_imp_mul: assumes "M -s dm r {#\<alpha>#} = {#}" shows "(M,{#\<alpha>#}) \<in> mul r" proof -
 from assms have C: "set_mset M \<subseteq> dm r {#\<alpha>#}" by (metis remove_empty_implies_subset)
 have "M = {#}+M" and "{#\<alpha>#}={#}+{#\<alpha>#}" and "{#\<alpha>#} \<noteq> {#}" by auto
 thus ?thesis using C unfolding mul_def by fast
qed

text \<open>Lemma 2.6\<close>

lemma lemma2_6_1_set: "ds r (S \<union> T) = ds r S \<union> ds r T"
 unfolding set_mset_union ds_def by auto

lemma lemma2_6_1_list: "dl r (\<sigma>@\<tau>) = dl r \<sigma> \<union> dl r \<tau>"
 unfolding dl_def ds_def set_append by auto

lemma lemma2_6_1_multiset: "dm r (M + N) = dm r M \<union> dm r N"
 unfolding dm_def set_mset_union ds_def by auto

lemma lemma2_6_1_diff: "(dm r M) - ds r S \<subseteq> dm r (M -s S)"
 unfolding diff_def dm_def ds_def by (rule subsetI) auto

text \<open>missing but useful\<close>
lemma dl_monotone: "dl r (\<sigma>@\<tau>) \<subseteq> dl r (\<sigma>@\<tau>'@\<tau>)" unfolding lemma2_6_1_list by auto

text \<open>Lemma 2.6.2\<close>

lemma lemma2_6_2_a: assumes t: "trans r" and "M \<subseteq># N" shows "(M,N) \<in> mul_eq r" proof -
 from assms(2) obtain J where "N=M+J" by (metis assms(2) mset_subset_eq_exists_conv)
 hence "M = M + {#}" and "N = M + J" and "set_mset {#} \<subseteq> dm r J" by auto
 thus ?thesis unfolding mul_eq_def by fast
qed

lemma mul_eq_not_equal_imp_elt:
assumes "(M,N)\<in>mul_eq r" and "y\<in>set_mset M - set_mset N" shows "\<exists>z\<in>set_mset N.(y,z)\<in>r" proof -
 from assms obtain I J K where "N=I+J" and "M=I+K" and F3:"set_mset K \<subseteq> dm r J" unfolding mul_eq_def by auto
 thus ?thesis using assms(2) downset_elim[OF F3] by auto
qed

lemma lemma2_6_2_b: assumes "trans r" and "(M,N) \<in> mul_eq r" shows "dm r M \<subseteq> dm r N" proof
 fix x assume A: "x \<in> dm r M" show "x \<in> dm r N" proof -
  from A obtain y where F2:"y\<in>set_mset M" and F3:"(x,y)\<in>r" unfolding dm_def ds_def by auto
  hence "\<exists> z \<in> set_mset N. (x,z)\<in>r" proof (cases "y\<in>set_mset N")
   case True thus ?thesis using F3 unfolding ds_def by auto
   next
   case False thus ?thesis using mul_eq_not_equal_imp_elt assms F2 F3 trans_def by fast
  qed
  thus ?thesis unfolding dm_def ds_def by auto
 qed
qed

text \<open>Lemma 2.6.3\<close>
lemma ds_trans_contrapos: assumes t: "trans r" and "x \<notin> ds r S" and "(x,y) \<in> r" shows "y \<notin> ds r S"
 using assms unfolding ds_def trans_def by fast

lemma dm_max_elt: assumes i: "irrefl r" and t: "trans r"  shows "x \<in> dm r M \<Longrightarrow> \<exists> y \<in> set_mset (M -s dm r M). (x,y) \<in> r"
 proof (induct M arbitrary: x)
  case empty thus ?case unfolding dm_def ds_def by auto
 next
  case (add p P)
  hence mem: "x \<in> (dm r P \<union> dm r {#p#})" unfolding dm_def ds_def by auto
  from i t have not_mem_dm: "p \<notin> dm r {#p#}" unfolding dm_def ds_def irrefl_def by auto
  thus ?case
  proof (cases "x \<in> dm r P")
   case False hence relp: "(x,p) \<in> r" using mem unfolding dm_def ds_def by auto
   show ?thesis proof (cases "p \<in> dm r P")
    case True thus ?thesis using relp t ds_trans_contrapos False unfolding dm_def by fast
     next
    case False thus ?thesis using not_mem_dm relp unfolding dm_def ds_def diff_def by auto
   qed
  next
    case True obtain y where key: "y \<in> set_mset P" "y \<notin> dm r P" "(x,y) \<in> r" using add(1)[OF True] unfolding diff_def by auto
    thus ?thesis
    proof (cases "y \<in> dm r {#p#}")
     case True hence rely: "(y,p) \<in> r" unfolding dm_def ds_def by auto
     hence relp: "(x,p) \<in> r" using rely t key trans_def by metis
     have not_memp: "p \<notin> set_mset P" using rely key unfolding dm_def ds_def by auto
     have memp: "p \<in> set_mset (P + {#p#})" by auto
     have "p \<notin> dm r P" using ds_trans_contrapos[OF t] key(2) rely unfolding dm_def by auto
     hence "p \<notin> dm r (P + {#p#})" using not_mem_dm unfolding dm_def ds_def by auto
     thus ?thesis using relp unfolding diff_def by auto
    next
     case False thus ?thesis using key unfolding dm_def ds_def diff_def by auto
    qed
  qed
 qed

lemma dm_subset: assumes i:"irrefl r" and t: "trans r"  shows "dm r M \<subseteq> dm r (M -s dm r M)"
 using assms dm_max_elt unfolding dm_def ds_def by fast

lemma dm_eq: assumes i:"irrefl r" and t: "trans r" shows "dm r M = dm r (M -s dm r M)"
 using dm_subset[OF assms] unfolding dm_def ds_def diff_def by auto

lemma lemma2_6_3: assumes t:"trans r" and i:"irrefl r" and "(M,N) \<in> mul_eq r"
 shows "\<exists> I' J' K' . N = I' + J' \<and> M = I' + K' \<and> J' \<inter># K' = {#} \<and> set_mset K' \<subseteq> dm r J'"
proof -
 from assms obtain I J K where 1:"N = I + J" and 2:"M = I + K"  and 3:"set_mset K \<subseteq> dm r J" unfolding mul_eq_def by auto
 have "set_mset (J \<inter># K) \<subseteq> r \<down>m J" using 3 by auto
 then obtain A where "r \<down>m J = set_mset (J \<inter># K) \<union> A"
  by blast
 then have key: "set_mset (J -s dm r J) \<subseteq> set_mset (J - (J \<inter># K))"
  by clarsimp (metis Multiset.count_diff add.left_neutral add_diff_cancel_left' mem_Collect_eq not_gr0 set_mset_def)
 from 1 2 3 have "N = (I + (J \<inter># K)) + (J - (J \<inter># K))"
  by (metis diff_union_cancelL subset_mset.inf_le2 multiset_diff_union_assoc multiset_inter_commute union_commute union_lcomm)
 moreover have "M = (I + (J \<inter># K)) + (K - (J \<inter># K))"
  by (metis diff_subset_eq_self diff_union_cancelL 2 multiset_diff_union_assoc multiset_inter_commute multiset_inter_def union_assoc)
 moreover have "set_mset (K-(J\<inter>#K)) \<subseteq> dm r (J-(J\<inter>#K))"
 proof -
  have "set_mset (K-(J\<inter>#K)) \<subseteq> dm r J" using 3
    by (meson Multiset.diff_subset_eq_self mset_subset_eqD subset_eq)
  moreover have "... = dm r (J -s dm r J)" using dm_eq[OF i t] by auto
  moreover have "... \<subseteq> dm r (J - (J \<inter># K))" using ds_monotone[OF key] unfolding dm_def by auto
  ultimately show ?thesis by auto
qed
 moreover have "(J-(J\<inter>#K)) \<inter># (K-(J\<inter>#K)) = {#}" by (rule multiset_eqI) auto
 ultimately show ?thesis by auto
qed

(*  (* initial proof by Bertram Felgenhauer *)
lemma lemma2_6_3_step:
assumes t:"trans r" and i:"irrefl r" and P:"set_mset K \<subseteq> dm r J" shows "set_mset (K-(J\<inter>#K)) \<subseteq> dm r (J-(J\<inter>#K))" proof
 fix k assume K: "k \<in> set_mset (K - (J\<inter>#K))" show "k \<in> dm r (J - (J\<inter>#K))" proof -
  have k: "k \<in># K" using K by simp
  have step: "k \<in> dm r (J-K)" proof -
   {
   fix P have "P \<le> K \<Longrightarrow> k \<in> dm r (J-P)" using k proof (induct P arbitrary:k rule:multiset_induct)
    case empty thus ?case using P by auto
   next
    case (add Q q)
    have h1: "q \<in># K" and h2: "Q \<le> K" using mset_subset_eq_insertD[OF add(2)] by auto
    obtain j where mem1: "j\<in>set_mset (J - Q)" and rel1: "(k, j) \<in> r" using add(1)[OF h2 add(3)] unfolding dm_def ds_def by auto
    show ?case proof (cases "j \<in># J - (Q + {#q#})")
     case True thus ?thesis using rel1 unfolding dm_def ds_def by force
    next
     case False hence eq: "q = j" using mem1 by (cases "q = j") auto
     obtain j2 where mem2: "j2\<in>set_mset (J - Q)" and rel2: "(j, j2) \<in> r" using eq add(1)[OF h2 h1] unfolding dm_def ds_def by auto
     have rel: "(k,j2) \<in> r" using transD[OF assms(1) rel1 rel2] by auto
     have "j2 \<noteq> q" using rel2 eq i irrefl_def by fast
     thus ?thesis using rel mem2 unfolding dm_def ds_def by (cases "j2=k") auto
    qed
   qed
   }
   thus ?thesis by auto
  qed
  have eq: "J - K = J - (J \<inter># K)" by (rule multiset_eqI) auto
  show ?thesis using step unfolding eq dm_def ds_def by auto
 qed
qed

lemma lemma2_6_3: assumes t: "trans r" and i: "irrefl r" and "(M,N) \<in> mul_eq r"
shows "\<exists> I J K. N = I + J \<and> M = I + K \<and> J\<inter>#K = {#} \<and> set_mset K \<subseteq> dm r J" proof -
 from assms(1,3)
 obtain I J K where f1:"N = I + J" and f2:"M = I + K" and f3:"set_mset K \<subseteq> dm r J" unfolding mul_eq_def by fast
 hence "N = (I + (J \<inter># K)) + (J - (J \<inter># K))"
  by (metis diff_union_cancelL inf_le2 multiset_diff_union_assoc multiset_inter_commute union_commute union_lcomm)
 moreover have "M = (I + (J \<inter># K)) + (K - (J \<inter># K))"
  by (metis diff_le_self diff_union_cancelL f1 f2 f3 multiset_diff_union_assoc multiset_inter_commute multiset_inter_def union_assoc)
 moreover have "(J-(J\<inter>#K)) \<inter># (K-(J\<inter>#K)) = {#}" by (rule multiset_eqI) auto
 ultimately show ?thesis using lemma2_6_3_step[OF t i f3] by auto
qed
*)

text \<open>Lemma 2.6.4\<close>
lemma lemma2_6_4: assumes t: "trans r" and "N \<noteq> {#}" and "set_mset M \<subseteq> dm r N" shows "(M,N) \<in> mul r" proof -
 have "M = {#} + M" and "N = {#} + N" using assms by auto
 thus ?thesis using assms(2,3) unfolding mul_def by fast
qed

lemma lemma2_6_5_a: assumes t: "trans r" and "ds r S \<subseteq> S" and "(M,N) \<in> mul_eq r"
shows "(M -s S, N -s S) \<in> mul_eq r"
proof -
 from assms(1,3)
 obtain I J K where a: "N=I+J" and b:"M=I+K" and c:"set_mset K \<subseteq> dm r J" unfolding mul_eq_def by best
 from a b have "M -s S = I -s S + K -s S"
   "N -s S = I -s S + J -s S" by (auto simp add: lemmaA_3_8)
 moreover have "set_mset (K-sS) \<subseteq> dm r (J-sS)" proof -
  have "set_mset (K-sS) \<subseteq> set_mset (K-s (ds r S))" using assms(2) unfolding diff_def by auto
  moreover have "set_mset(K-s (ds r S)) \<subseteq> (dm r J) - (ds r S)" using c unfolding diff_def by auto
  moreover have "(dm r J) - (ds r S) \<subseteq> dm r (J -s S)" using lemma2_6_1_diff by fast
  ultimately show ?thesis by auto
 qed
 ultimately show ?thesis by (rule in_mul_eqI)
qed

lemma lemma2_6_5_a': assumes t:"trans r" and "(M,N) \<in> mul_eq r" shows "(M -s ds r S, N -s ds r S) \<in> mul_eq r"
  using assms lemma2_6_5_a[OF t] ds_ds_subseteq_ds[OF t] by auto

text \<open>Lemma 2.6.6\<close>
lemma lemma2_6_6_a: assumes t: "trans r" and "(M,N) \<in> mul_eq r" shows "(Q + M,Q + N) \<in> mul_eq r" proof -
 obtain I J K where A:"Q+N=(Q+I)+J" and B:"Q+M=(Q+I)+K" and C:"set_mset K \<subseteq> dm r J"
  using assms(2) unfolding mul_eq_def by auto
  thus ?thesis using C unfolding mul_eq_def by blast
qed

lemma add_left_one:
 assumes  "\<exists> I J K. add_mset q N = I + J \<and> add_mset q  M = I + K \<and> (J\<inter>#K={#}) \<and> set_mset K \<subseteq> dm r J"
 shows "\<exists> I2 J K. N = I2 + J \<and> M = I2 + K \<and> set_mset K \<subseteq> dm r J" proof -
 from assms obtain I J K where A: "{#q#} + N = I + J" and B:"{#q#} + M = I + K"
  and C:"(J \<inter># K = {#})" and D:"set_mset K \<subseteq> dm r J" by auto
 have "q\<in>#I" proof (cases "q \<in># I")
  case True thus ?thesis by auto
 next
  case False
  have "q \<in># J" using False A by (metis UnE multi_member_this set_mset_union) 
  moreover have "q \<in># K" using False B by (metis UnE multi_member_this set_mset_union)
  moreover have "\<not> q \<in># (J \<inter># K)" using C by auto
  ultimately show ?thesis by auto
 qed
 hence "\<exists> I2. I = add_mset q I2" by (metis multi_member_split union_commute)
 hence "\<exists> I2. add_mset q N = (add_mset q I2) + J \<and> add_mset q M = (add_mset q I2) + K" using A B by auto
 thus ?thesis using D by auto
qed

lemma lemma2_6_6_b_one :
assumes "trans r" and "irrefl r" and "(add_mset q M, add_mset q N) \<in> mul_eq r" shows "(M,N) \<in> mul_eq r"
 using add_left_one[OF lemma2_6_3[OF assms]] unfolding mul_eq_def by auto

lemma lemma2_6_6_b' : assumes "trans r" and i: "irrefl r" and "(Q + M, Q + N) \<in> mul_eq r"
 shows "(M,N) \<in> mul_eq r" using assms(3) proof (induct Q arbitrary: M N)
 case empty thus ?case by auto
 next
 case (add q Q) thus ?case unfolding union_assoc using lemma2_6_6_b_one[OF assms(1,2)]
   by (metis union_mset_add_mset_left)
 qed

lemma lemma2_6_9: assumes t: "trans r" and "(M,N) \<in> mul r" shows "(Q+M,Q+N) \<in> mul r" proof -
 obtain I J K where F1:"N = I + J" and F2:"M = I + K"and F3:"set_mset K \<subseteq> dm r J" and F4:"J \<noteq> {#}"
  using assms unfolding mul_def by auto
 have "Q+N=Q+I+J" and "Q+M=Q+I+K" by (auto simp: F1 F2 union_commute union_lcomm)
  thus ?thesis using assms(1) F3 F4 unfolding mul_def by blast
qed

text \<open>Lemma 2.6.7\<close>
lemma lemma2_6_7_a: assumes t: "trans r" and "set_mset Q \<subseteq> dm r N - dm r M" and "(M,N) \<in> mul_eq r"
shows "(Q+M,N) \<in> mul_eq r" proof -
 obtain I J K where A: "N=I+J" and B:"M=I+K" and C:"set_mset K \<subseteq> dm r J" using assms unfolding mul_eq_def by auto
 hence "set_mset(Q+K) \<subseteq> dm r J" using assms lemma2_6_1_diff unfolding dm_def ds_def by auto
 hence "(I+(Q+K),I+J) \<in> mul_eq r" unfolding mul_eq_def by fast
 thus ?thesis using A B C union_assoc union_commute by metis
qed

text \<open>missing?; similar to lemma\_2.6.2?\<close>
lemma lemma2_6_8: assumes t: "trans r" and "S \<subseteq> T" shows "(M -s T,M -s S) \<in> mul_eq r" proof -
 from assms(2) have "(M -s T) \<subseteq># (M -s S)"
  by (metis Un_absorb2 Un_commute lemmaA_3_10 lemmaA_3_9 mset_subset_eq_add_right)
 thus ?thesis using lemma2_6_2_a[OF t] by auto
qed

subsubsection \<open>Lexicographic maximum measure\<close>
text \<open>Def 3.1: lexicographic maximum measure\<close>
fun lexmax :: "'a rel \<Rightarrow> 'a list \<Rightarrow> 'a multiset" where
   "lexmax r [] = {#}"
 | "lexmax r (\<alpha>#\<sigma>) =  {#\<alpha>#} + (lexmax r \<sigma> -s ds r {\<alpha>})"

notation
 lexmax ("_|_|" [1000] 1000)

lemma lexmax_singleton: "r|[\<alpha>]| = {#\<alpha>#}" unfolding lexmax.simps diff_def by simp

text \<open>Lemma 3.2\<close>

text \<open>Lemma 3.2(1)\<close>
lemma lemma3_2_1: assumes t: "trans r" shows "r \<down>m r|\<sigma>| = r \<down>l \<sigma>" proof (induct \<sigma>)
 case Nil show ?case unfolding dm_def dl_def by auto
 next
 case (Cons \<alpha> \<sigma>)
 have "dm r {#\<alpha>#} \<union> dm r (r|\<sigma>| -s ds r {\<alpha>}) = dm r {#\<alpha>#} \<union> dl r \<sigma>" (is "?L = ?R") proof -
  have "?L \<subseteq> ?R" unfolding Cons[symmetric] diff_def dm_def ds_def by auto
  moreover have "?R \<subseteq> ?L" proof
   fix x assume A: "x \<in> ?R" show "x \<in> ?L" proof (cases "x \<in> dm r {#\<alpha>#}")
    case True thus ?thesis by auto
   next
    case False
    hence mem: "x \<in> dm r (lexmax r \<sigma>)" using A Cons by auto
    have "x \<notin> (ds r (ds r {\<alpha>}))" using False ds_ds_subseteq_ds[OF t] unfolding dm_def by auto
    thus ?thesis using mem lemma2_6_1_diff by fast
   qed
  qed
  ultimately show ?thesis by auto
 qed
 thus ?case unfolding lemma2_6_1_multiset lexmax.simps dl_def dm_def ds_def by auto
qed

text \<open>Lemma 3.2(2)\<close>
lemma lemma3_2_2: "r|\<sigma>@\<tau>| = r|\<sigma>| + (r|\<tau>| -s r \<down>l \<sigma>)" proof(induct \<sigma>)
 case Nil thus ?case unfolding dl_def ds_def lexmax.simps apply auto unfolding diff_empty by auto
 next
 case (Cons \<alpha> \<sigma>)
  have "lexmax r (\<alpha>#\<sigma>@\<tau>) = {#\<alpha>#} + ((lexmax r (\<sigma>@\<tau>)) -s (ds r {\<alpha>}))" by auto
  moreover have "\<dots> = {#\<alpha>#} + ((lexmax r \<sigma> + ((lexmax r \<tau>) -s (dl r \<sigma>))) -s (ds r {\<alpha>}))"
   using Cons by auto
  moreover have "\<dots> = {#\<alpha>#} + ((lexmax r \<sigma>) -s (ds r {\<alpha>})) + (((lexmax r \<tau>) -s (dl r \<sigma>)) -s (ds r {\<alpha>}))"
   unfolding lemmaA_3_8 unfolding union_assoc by auto
  moreover have "\<dots> = lexmax r (\<alpha>#\<sigma>) + (((lexmax r \<tau>) -s (dl r \<sigma>)) -s (ds r {\<alpha>}))" by simp
  moreover have "\<dots> = lexmax r (\<alpha>#\<sigma>) + ((lexmax r \<tau>) -s (dl r (\<alpha>#\<sigma>)))" unfolding lemmaA_3_9 dl_def dm_def lemma2_6_1_set[symmetric] by auto
  ultimately show ?case unfolding diff_def by simp
qed

text \<open>Definition 3.3\<close>

definition D :: "'a rel \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
 "D r \<tau> \<sigma> \<sigma>' \<tau>' = ((r|\<sigma>@\<tau>'|, r|\<tau>| + r|\<sigma>| ) \<in> mul_eq r
                 \<and> (r|\<tau>@\<sigma>'|, r|\<tau>| + r|\<sigma>| ) \<in> mul_eq r)"

lemma D_eq: assumes "trans r" and "irrefl r" and "D r \<tau> \<sigma> \<sigma>' \<tau>'"
 shows "(r|\<tau>'| -s dl r \<sigma>,r|\<tau>| ) \<in> mul_eq r" and "(r|\<sigma>'| -s dl r \<tau>,r|\<sigma>| ) \<in> mul_eq r"
 using assms unfolding D_def lemma3_2_2 using union_commute lemma2_6_6_b' apply metis
 using assms unfolding D_def lemma3_2_2 using union_commute lemma2_6_6_b' by metis

lemma D_inv: assumes "trans r" and "irrefl r" and "(r|\<tau>'| -s dl r \<sigma>,r|\<tau>| ) \<in> mul_eq r"
                                                and "(r|\<sigma>'| -s dl r \<tau>,r|\<sigma>| ) \<in> mul_eq r"
 shows "D r \<tau> \<sigma> \<sigma>' \<tau>'"
 using assms unfolding D_def lemma3_2_2 using lemma2_6_6_a[OF assms(1)] union_commute by metis

lemma D: assumes "trans r" and "irrefl r"
 shows  "D r \<tau> \<sigma> \<sigma>' \<tau>' = ((r|\<tau>'| -s dl r \<sigma>,r|\<tau>| ) \<in> mul_eq r
                        \<and> (r|\<sigma>'| -s dl r \<tau>,r|\<sigma>| ) \<in> mul_eq r)"
 using assms D_eq D_inv by auto

lemma mirror_D: assumes "trans r" and "irrefl r" and "D r \<tau> \<sigma> \<sigma>' \<tau>'" shows "D r \<sigma> \<tau> \<tau>' \<sigma>'"
 using assms D by metis

text \<open>Proposition 3.4\<close>

definition LD_1' :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
 where "LD_1' r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 =
 (set \<sigma>1 \<subseteq> ds r {\<beta>} \<and> length \<sigma>2 \<le> 1 \<and> set \<sigma>2 \<subseteq> {\<alpha>} \<and> set \<sigma>3 \<subseteq> ds r {\<alpha>,\<beta>})"

definition LD' :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a
  \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
 where "LD' r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3 = (LD_1' r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 \<and> LD_1' r \<alpha> \<beta> \<tau>1 \<tau>2 \<tau>3)"

text \<open>auxiliary properties on multisets\<close>

lemma lexmax_le_multiset: assumes t:"trans r" shows "r|\<sigma>| \<subseteq># mset \<sigma>" proof (induct "\<sigma>")
 case Nil thus ?case unfolding lexmax.simps by auto
 next
 case (Cons s \<tau>) hence "lexmax r \<tau> -s ds r {s} \<subseteq># mset \<tau>" using lemmaA_3_10 mset_subset_eq_add_right subset_mset.order_trans by metis
 thus ?case by simp
qed

lemma split: assumes "LD_1' r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3" shows "\<sigma>2 = [] \<or> \<sigma>2 = [\<alpha>]"
 using assms unfolding  LD_1'_def by (cases \<sigma>2) auto

lemma proposition3_4_step: assumes "trans r" and "irrefl r" and "LD_1' r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3"
shows "(r|\<sigma>1@\<sigma>2@\<sigma>3| -s (dm r {#\<beta>#}), r|[\<alpha>]| ) \<in> mul_eq r" proof -
 from assms have "set \<sigma>1 \<subseteq> dm r {#\<beta>#}" unfolding LD'_def LD_1'_def dm_def by auto
 hence "set_mset (lexmax r \<sigma>1) \<subseteq> dm r {#\<beta>#}" using submultiset_implies_subset[OF lexmax_le_multiset[OF assms(1)]] by auto
 hence one: "lexmax r \<sigma>1 -s dm r {#\<beta>#} = {#}" using subset_implies_remove_empty by auto
 from assms have "set \<sigma>3 \<subseteq> dl r \<sigma>2 \<union> dl r \<sigma>1 \<union> dm r {#\<beta>#} \<union> dm r {#\<alpha>#}" (is "?l \<subseteq> ?r") unfolding LD'_def LD_1'_def dm_def ds_def by auto
 hence "set_mset (lexmax r \<sigma>3) \<subseteq> ?r " using submultiset_implies_subset[OF lexmax_le_multiset[OF assms(1)]] by auto
 hence pre3: "lexmax r \<sigma>3 -s ?r = {#}" using subset_implies_remove_empty by auto
 show ?thesis proof (cases "\<sigma>2 = []")
  case True
  hence two:"(lexmax r \<sigma>2 -s dl r \<sigma>1) -s dm r {#\<beta>#} = {#}" unfolding diff_def by auto
  from pre3 have "(((lexmax r \<sigma>3 -s dl r \<sigma>2) -s dl r \<sigma>1) -s dm r {#\<beta>#}) -s dm r {#\<alpha>#} = {#}" unfolding True dl_def lemmaA_3_9 by auto
  hence three:"(((lexmax r \<sigma>3 -s dl r \<sigma>2) -s dl r \<sigma>1) -s dm r {#\<beta>#},{#\<alpha>#}) \<in> mul r" using remove_is_empty_imp_mul by metis
  show ?thesis using three unfolding lemma3_2_2 lexmax_singleton lemmaA_3_8 one two mul_def mul_eq_def by auto
 next
  case False hence eq: "\<sigma>2 = [\<alpha>]" using split[OF assms(3)] by fast
  have two: "((lexmax r \<sigma>2 -s dl r \<sigma>1) -s dm r {#\<beta>#},{#\<alpha>#}) \<in> mul_eq r" using lemma2_6_8[OF assms(1) empty_subsetI] unfolding eq lexmax.simps diff_from_empty lemmaA_3_9 diff_empty by auto
  from pre3 have "lexmax r \<sigma>3 -s ((dl r \<sigma>2 \<union> dm r {#\<alpha>#}) \<union> dl r \<sigma>1 \<union> dm r {#\<beta>#}) = {#}" unfolding eq lemmaA_3_9 using Un_assoc Un_commute by metis
  hence three: "((lexmax r \<sigma>3 -s dl r \<sigma>2) -s dl r \<sigma>1) -s dm r {#\<beta>#} = {#}" using Un_absorb unfolding lemmaA_3_9 eq dm_def dl_def by auto
  show ?thesis unfolding lemma3_2_2 lexmax_singleton lemmaA_3_8 one three using two by auto
 qed
qed

lemma proposition3_4:
assumes t: "trans r" and i: "irrefl r" and ld: "LD' r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3"
shows "D r [\<beta>] [\<alpha>] (\<sigma>1@\<sigma>2@\<sigma>3) (\<tau>1@\<tau>2@\<tau>3)"
 using proposition3_4_step[OF t i] ld unfolding LD'_def D[OF assms(1,2)] dl_def dm_def by auto

(*reverse direction*)

lemma lexmax_decompose: assumes "\<alpha> \<in># r|\<sigma>|" shows "\<exists>\<sigma>1 \<sigma>3. (\<sigma>=\<sigma>1@[\<alpha>]@\<sigma>3 \<and> \<alpha> \<notin> dl r \<sigma>1)"
using assms proof (induct \<sigma>)
 case Nil thus ?case by auto
 next
 case (Cons \<beta> as) thus ?case proof (cases "\<alpha>=\<beta>")
  case True
  from this obtain \<sigma>1 \<sigma>3 where dec: "\<beta>#as = \<sigma>1@[\<alpha>]@\<sigma>3" and empty: "\<sigma>1 = []" by auto
  hence "\<alpha> \<notin> dl r \<sigma>1" unfolding dl_def ds_def by auto
  thus ?thesis using dec by auto
 next
  case False hence "\<alpha> \<in># r|as|-s ds r {\<beta>}" using Cons(2) by auto
  hence x: "\<alpha> \<in># r|as| \<and> \<alpha> \<notin> ds r {\<beta>}"
    by simp
  from this obtain \<sigma>1 \<sigma>3 where "as = \<sigma>1 @ [\<alpha>] @ \<sigma>3" and w: "\<alpha> \<notin> dl r \<sigma>1" using Cons(1) by auto
  hence  "\<beta>#as = (\<beta>#\<sigma>1) @ [\<alpha>] @ \<sigma>3" and  "\<alpha> \<notin> dl r (\<beta>#\<sigma>1)" using x w unfolding dm_def dl_def ds_def by auto
  thus ?thesis by fast
 qed
qed

lemma lexmax_elt: assumes "trans r" and "x \<in> (set \<sigma>)" and "x \<notin> set_mset r|\<sigma>|"
shows "\<exists>y. (x,y) \<in> r \<and> y \<in> set_mset r|\<sigma>|"  using assms(2,3) proof (induct \<sigma>)
 case Nil thus ?case by auto
next
 case (Cons a as) thus ?case proof (cases "x \<notin> set_mset r|as|")
   case True
   from Cons True obtain y where s: "(x, y) \<in> r \<and> y \<in> set_mset r|as|" by auto
   thus ?thesis proof (cases "y \<in> ds r {a}")
    case True thus ?thesis using transD[OF assms(1)] s unfolding dm_def ds_def by auto
   next
    case False thus ?thesis using s unfolding lexmax.simps diff_def by auto
   qed
  next
   case False thus ?thesis using Cons unfolding diff_def dm_def ds_def lexmax.simps by auto
  qed
 qed

lemma lexmax_set: assumes "trans r" and "set_mset r|\<sigma>| \<subseteq> r \<down>s S" shows "set \<sigma> \<subseteq> r \<down>s S" proof
 fix x assume A: "x \<in> set \<sigma>" show "x \<in> ds r S" proof (cases "x \<in> set_mset r|\<sigma>|")
  case True thus ?thesis using assms by auto
 next
  case False from lexmax_elt[OF assms(1) A False] obtain y
  where rel: "(x,y) \<in> r \<and> y \<in> set_mset r|\<sigma>|" by auto
  hence "y \<in> ds r S" using assms by auto
  thus ?thesis using rel assms transD unfolding dm_def ds_def by fast
 qed
qed

lemma drop_left_mult_eq:
assumes "trans r" and "irrefl r" and "(N+M,M) \<in> mul_eq r" shows "N = {#}" proof -
 have "(M+N,M+{#}) \<in> mul_eq r" using assms(3) apply auto using union_commute by metis
 hence k:"(N,{#}) \<in> mul_eq r" using lemma2_6_6_b'[OF assms(1,2)] by fast
 from this obtain I J K where "{#} = I + J \<and> N = I + K \<and> set_mset K \<subseteq> dm r J" unfolding mul_eq_def by fast
 thus ?thesis unfolding dm_def ds_def by auto
qed

text \<open>generalized to lists\<close>
lemma proposition3_4_inv_lists:
assumes t: "trans r" and i: "irrefl r" and k:"(r|\<sigma>| -s r \<down>l \<beta>, {#\<alpha>#}) \<in> mul_eq r" (is "(?M,_) \<in> _")
shows "\<exists> \<sigma>1 \<sigma>2 \<sigma>3. ((\<sigma> = \<sigma>1@\<sigma>2@\<sigma>3) \<and> set \<sigma>1 \<subseteq> dl r \<beta> \<and> length \<sigma>2 \<le> 1 \<and> set \<sigma>2 \<subseteq> {\<alpha>}) \<and> set \<sigma>3 \<subseteq> dl r (\<alpha>#\<beta>)"  proof (cases "\<alpha> \<in># ?M")
  case True hence "\<alpha> \<in># r|\<sigma>|" by simp
  from this obtain \<sigma>1 \<sigma>3 where sigma: "\<sigma>=\<sigma>1@[\<alpha>]@\<sigma>3" and alpha: "\<alpha> \<notin> dl r \<sigma>1" using lexmax_decompose by metis
  hence dec: "((r|\<sigma>1|-sdl r \<beta>) + (r|[\<alpha>]|-s (dl r \<sigma>1 \<union> dl r \<beta>)) + (r|\<sigma>3| -s (dl r [\<alpha>] \<union> dl r \<sigma>1 \<union> dl r \<beta>)), {#\<alpha>#}) \<in> mul_eq r" (is "(?M1 + ?M2 + ?M3,_) \<in> _")
   using k unfolding sigma lemma3_2_2 lemmaA_3_8 lemmaA_3_9 LD_1'_def union_assoc by auto

  from True have key: "\<alpha> \<notin> dl r \<beta>" by simp
  hence "?M2 = {#\<alpha>#}" unfolding lexmax_singleton diff_def using alpha by auto
  hence "(?M1+?M3 + {#\<alpha>#},{#\<alpha>#}) \<in> mul_eq r" using dec union_assoc union_commute by metis
  hence w: "?M1+?M3 = {#}" using drop_left_mult_eq assms(1,2) by blast
  from w have "(r|\<sigma>1|-sdl r \<beta>) = {#}" by auto
  hence "set_mset r|\<sigma>1| \<subseteq> ds r (set \<beta>)" using remove_empty_implies_subset unfolding dl_def dm_def by auto
  hence sigma1: "set \<sigma>1 \<subseteq> ds r (set \<beta>)" using lexmax_set[OF assms(1)] by auto

  have sigma2: "length [\<alpha>] \<le> 1 \<and> set [\<alpha>] \<subseteq> {\<alpha>}" by auto

  have sub:"dl r \<sigma>1 \<subseteq> dl r \<beta>" using subset_imp_ds_subset[OF assms(1) sigma1] unfolding dm_def dl_def by auto
  hence sub2: "dl r \<sigma>1 \<union> dl r \<beta> = dl r \<beta>" by auto
  from w have  "?M3 = {#}" by auto
  hence "r|\<sigma>3|-s (ds r {\<alpha>} \<union> ds r (set \<beta>)) = {#}" unfolding Un_assoc sub2 unfolding dl_def by auto
  hence "r|\<sigma>3|-s (ds r ({\<alpha>} \<union> (set \<beta>))) = {#}" unfolding lemma2_6_1_set[symmetric] by metis
  hence "set_mset r|\<sigma>3| \<subseteq> ds r ({\<alpha>} \<union> (set \<beta>))" using remove_empty_implies_subset by auto
  hence sigma3: "set \<sigma>3 \<subseteq> ds r ({\<alpha>} \<union> (set \<beta>))" using lexmax_set[OF assms(1)] by auto
  show ?thesis using sigma sigma1 sigma2 sigma3 unfolding dl_def apply auto by (metis One_nat_def append_Cons append_Nil sigma2)
 next
  case False hence "set_mset ?M \<subseteq> dm r {#\<alpha>#}" using mul_eq_singleton[OF k]
    by (auto dest: diff_eq_singleton_imp)
  hence "set_mset r|\<sigma>| \<subseteq> ds r ({\<alpha>} \<union> (set \<beta>))" unfolding diff_def dm_def dl_def ds_def by auto
  hence "set \<sigma> \<subseteq> ds r ({\<alpha>} \<union> (set \<beta>))" using lexmax_set[OF assms(1)] by auto
  thus ?thesis unfolding dl_def apply auto by (metis append_Nil bot_least empty_set le0 length_0_conv)
 qed

lemma proposition3_4_inv_step:
assumes t: "trans r" and i: "irrefl r" and k:"(r|\<sigma>| -s r \<down>l [\<beta>], {#\<alpha>#}) \<in> mul_eq r" (is "(?M,_) \<in> _")
shows "\<exists> \<sigma>1 \<sigma>2 \<sigma>3. ((\<sigma> = \<sigma>1@\<sigma>2@\<sigma>3) \<and> LD_1' r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3)"
 using proposition3_4_inv_lists[OF assms] unfolding LD_1'_def dl_def by auto

lemma proposition3_4_inv:
assumes t: "trans r" and i: "irrefl r" and "D r [\<beta>] [\<alpha>] \<sigma> \<tau>"
shows "\<exists> \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3. (\<sigma> = \<sigma>1@\<sigma>2@\<sigma>3 \<and> \<tau> = \<tau>1@\<tau>2@\<tau>3 \<and> LD' r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3)"
using proposition3_4_inv_step[OF assms(1,2)] D_eq[OF assms] unfolding lexmax_singleton LD'_def by metis

text \<open>Lemma 3.5\<close>
lemma lemma3_5_1:
assumes t: "trans r" and "irrefl r" and "D r \<tau> \<sigma> \<sigma>' \<tau>'" and "D r \<upsilon> \<sigma>' \<sigma>'' \<upsilon>'"
shows "(lexmax r (\<tau> @ \<upsilon> @ \<sigma>''), lexmax r (\<tau> @ \<upsilon>) + lexmax r \<sigma>) \<in> mul_eq r" proof -
 have "lexmax r (\<tau> @ \<upsilon> @ \<sigma>'') = (lexmax r (\<tau> @ \<upsilon>) + ((lexmax r \<sigma>'') -s (dl r (\<tau>@\<upsilon>))))"
  unfolding append_assoc[symmetric] using lemma3_2_2 by fast
 moreover have x:"\<dots> = lexmax r (\<tau>@\<upsilon>) + (((lexmax r \<sigma>'') -s dl r \<upsilon>) -s dl r \<tau>)"
  by (auto simp: lemma2_6_1_list lemmaA_3_9 Un_commute)
 moreover have "(\<dots>,lexmax r (\<tau>@\<upsilon>) + (lexmax r \<sigma>' -s dl r \<tau>)) \<in> mul_eq r" (is "(_,?R) \<in> _")
  using lemma2_6_6_a[OF t lemma2_6_5_a'[OF t D_eq(2)[OF assms(1,2,4)]]] unfolding dl_def by auto
 moreover have "(?R,lexmax r (\<tau>@\<upsilon>) + lexmax r \<sigma>) \<in> mul_eq r"
  using lemma2_6_6_a[OF t D_eq(2)[OF assms(1-3)]] by auto
 ultimately show ?thesis using mul_eq_trans[OF t] by metis
 qed

lemma claim1: assumes t: "trans r" and "D r \<tau> \<sigma> \<sigma>' \<tau>'"
shows "(r|\<sigma>@\<tau>'| + ((r|\<upsilon>'| -s r \<down>l (\<sigma>@\<tau>')) \<inter>s r \<down>l \<tau>),r|\<sigma>| + r|\<tau>| ) \<in> mul_eq r" (is "(?F+?H,?G) \<in> _")
proof -
 have 1: "(?F,?G) \<in> mul_eq r" using assms(2) unfolding D_def by (auto simp: union_commute)
 have 2: "set_mset ?H \<subseteq> (dm r ?G) - (dm r ?F)" (is "(?L \<subseteq> _)") proof -
  have "set_mset ?H = set_mset ((lexmax r \<upsilon>' \<inter>s dl r \<tau>) -s dl r (\<sigma>@\<tau>'))" unfolding lemmaA_3_11 by auto
  moreover have  "\<dots> \<subseteq> (dl r \<tau> - dl r (\<sigma>@\<tau>'))" unfolding diff_def intersect_def by auto
  moreover have "... \<subseteq> ((dl r \<sigma> \<union> dl r \<tau>) - dl r (\<sigma>@\<tau>'))" by auto
  ultimately show ?thesis unfolding lemma2_6_1_multiset lemma3_2_1[OF t] by auto
 qed
show ?thesis using lemma2_6_7_a[OF t 2 1] by (auto simp: union_commute)
qed

lemma step3: assumes t:"trans r" and "D r \<tau> \<sigma> \<sigma>' \<tau>'"
shows "r \<down>l (\<sigma>@\<tau>) \<supseteq> (r \<down>m (r|\<sigma>'| + r|\<tau>| ))" proof -
 have a: "dl r (\<sigma>@\<tau>) = dm r (lexmax r \<tau> + lexmax r \<sigma>)" and b: "dl r (\<tau>@\<sigma>') = dm r (lexmax r \<sigma>' + lexmax r \<tau>)"
   unfolding lemma2_6_1_list lemma3_2_1[OF t,symmetric] lemma2_6_1_multiset by auto
 show ?thesis using assms(2) lemma2_6_2_b[OF t] lemma3_2_1[OF t,symmetric] unfolding D_def a b[symmetric] by auto
qed

lemma claim2: assumes t: "trans r" and "D r \<tau> \<sigma> \<sigma>' \<tau>'"
shows "((r|\<upsilon>'| -s  r \<down>l (\<sigma>@\<tau>')) -s r \<down>l \<tau>, (r|\<upsilon>'| -s r \<down>l \<sigma>') -s r \<down>l \<tau>) \<in> mul_eq r" (is "(?L,?R) \<in> _")
 proof -
  have "?L = lexmax r \<upsilon>' -s (dl r (\<sigma>@\<tau>'@\<tau>))" unfolding lemmaA_3_9 append_assoc[symmetric] lemma2_6_1_list by auto
  moreover have "(\<dots>,lexmax r \<upsilon>' -s dl r (\<sigma>@\<tau>)) \<in> mul_eq r" (is "(_,?R) \<in> _") using lemma2_6_8[OF t dl_monotone] by auto
  moreover have  "(?R,lexmax r \<upsilon>' -s dm r (lexmax r \<sigma>' + lexmax r \<tau>)) \<in> mul_eq r" (is "(_,?R) \<in> _") using lemma2_6_8[OF t step3[OF assms]] by auto
  moreover have "?R = (lexmax r \<upsilon>' -s dl r \<sigma>') -s dl r \<tau>" unfolding lemma3_2_1[OF t,symmetric] lemma2_6_1_multiset lemmaA_3_9[symmetric] by auto
  ultimately show ?thesis using mul_eq_trans[OF t] by metis
 qed

lemma lemma3_5_2: assumes "trans r" and "irrefl r" and "D r \<tau> \<sigma> \<sigma>' \<tau>'" and "D r \<upsilon> \<sigma>' \<sigma>'' \<upsilon>'"
 shows "(r|(\<sigma> @ \<tau>' @ \<upsilon>')|, r|\<sigma>| + r|(\<tau>@\<upsilon>)| ) \<in> mul_eq r"
proof -
 have 0: "lexmax r (\<sigma>@\<tau>'@\<upsilon>') = lexmax r (\<sigma>@\<tau>') + (lexmax r \<upsilon>' -s dl r (\<sigma>@\<tau>'))" (is "?L = _")
  unfolding append_assoc[symmetric] lemma3_2_2 by auto
 moreover have "\<dots> = lexmax r (\<sigma>@\<tau>') + ((lexmax r \<upsilon>' -s dl r (\<sigma>@\<tau>')) \<inter>s dl r \<tau>) + ((lexmax r \<upsilon>' -s dl r (\<sigma>@\<tau>')) -s dl r \<tau>)"
  using lemmaA_3_10 unfolding union_assoc by auto
 moreover have "(\<dots>, lexmax r \<sigma> + lexmax r \<tau> + ((lexmax r \<upsilon>' -s dl r (\<sigma>@\<tau>')) -s dl r \<tau>)) \<in> mul_eq r" (is "(_,?R) \<in> _")
  using assms claim1 lemma2_6_6_a union_commute by metis
 moreover have "(?R, lexmax r \<sigma> + lexmax r \<tau> + (((lexmax r \<upsilon>' -s dl r \<sigma>') -s dl r \<tau>))) \<in> mul_eq r" (is "(_,?R) \<in> _")
  using lemma2_6_6_a[OF assms(1) claim2[OF assms(1,3)]] by auto
 moreover have "(?R, lexmax r \<sigma> + lexmax r \<tau> + lexmax r \<upsilon> -s dl r \<tau>) \<in> mul_eq r" (is "(_,?R) \<in> _")
  using lemma2_6_6_a[OF assms(1) lemma2_6_5_a'[OF assms(1) D_eq(1)[OF assms(1,2,4)]]] unfolding dl_def by auto
 moreover have "?R = lexmax r \<sigma> + lexmax r (\<tau>@\<upsilon>)" unfolding union_assoc lemma3_2_2 by auto
 ultimately show ?thesis using mul_eq_trans[OF assms(1)] by metis
qed

lemma lemma3_5: assumes "trans r" and "irrefl r" and "D r \<tau> \<sigma> \<sigma>' \<tau>'" and "D r \<upsilon> \<sigma>' \<sigma>'' \<upsilon>'"
shows "D r (\<tau>@\<upsilon>) \<sigma> \<sigma>'' (\<tau>'@\<upsilon>')"
 unfolding D_def append_assoc using assms lemma3_5_1 lemma3_5_2 union_commute by metis

lemma step2: assumes "trans r" and "\<tau> \<noteq> []" shows "(M \<inter>s dl r \<tau>,lexmax r \<tau>) \<in> mul r" proof -
 from assms obtain x xs where "\<tau>=x#xs" using list.exhaust by auto
 hence x: "lexmax r \<tau> \<noteq> {#}" by auto
 from assms(2) have y: "set_mset (M \<inter>sdl r \<tau>) \<subseteq> dm r (lexmax r \<tau>)" unfolding lemma3_2_1[OF assms(1)] intersect_def by auto
 show ?thesis using lemma2_6_4[OF assms(1) x y] by auto
qed

text \<open>Lemma 3.6\<close>
lemma lemma3_6: assumes t: "trans r" and ne: "\<tau> \<noteq> []" and D: "D r \<tau> \<sigma> \<sigma>' \<tau>'"
shows "(r|\<sigma>'| + r|\<upsilon>|, r|\<sigma>| + r|\<tau>@\<upsilon>| ) \<in> mul r" (is "(?L,?R) \<in> _") proof -
 have "?L = ((lexmax r \<sigma>' + lexmax r \<upsilon>) \<inter>s dl r \<tau>) + ((lexmax r \<sigma>' + lexmax r \<upsilon>) -s dl r \<tau>)"
  unfolding lemmaA_3_10[symmetric] by auto
 moreover have "(\<dots>,lexmax r \<tau> + ((lexmax r \<sigma>' + lexmax r \<upsilon>) -s dl r \<tau>)) \<in> mul r" (is "(_,?R2) \<in> _")
  using lemma2_6_9[OF t step2[OF t ne]] union_commute by metis
 moreover have "?R2 = lexmax r \<tau> + (lexmax r \<sigma>' -s dl r \<tau>) + (lexmax r \<upsilon> -s dl r \<tau>)"
  unfolding lemmaA_3_8 union_assoc[symmetric] by auto
 moreover have "\<dots> = lexmax r (\<tau>@\<sigma>') + (lexmax r \<upsilon> -s dl r \<tau>)" unfolding lemma3_2_2 by auto
 moreover have "(\<dots>,lexmax r \<sigma> + lexmax r \<tau> + (lexmax r \<upsilon> -s dl r \<tau>)) \<in> mul_eq r" (is "(_,?R5) \<in> _")
  using D unfolding D_def using lemma2_6_6_a[OF t] union_commute by metis
 moreover have "?R5 = ?R" unfolding lemma3_2_2 union_assoc by auto
 ultimately show ?thesis using mul_and_mul_eq_imp_mul t by metis
qed

lemma lemma3_6_v: assumes "trans r" and "irrefl r" and "\<sigma> \<noteq> []" and "D r \<tau> \<sigma> \<sigma>' \<tau>'"
shows "(r|\<tau>'| + r|\<upsilon>|, r|\<tau>| + r|\<sigma>@\<upsilon>| ) \<in> mul r"
 using assms lemma3_6 mirror_D by fast

subsubsection \<open>Labeled Rewriting\<close>

text \<open>Theorem 3.7\<close>
type_synonym ('a,'b) lars = "('a\<times>'b\<times>'a) set"
type_synonym ('a,'b) seq = "('a\<times>('b\<times>'a)list)"

inductive_set seq :: "('a,'b) lars \<Rightarrow> ('a,'b) seq set" for ars
 where "(a,[]) \<in> seq ars"
     | "(a,\<alpha>,b) \<in> ars \<Longrightarrow> (b,ss) \<in> seq ars \<Longrightarrow> (a,(\<alpha>,b) # ss) \<in> seq ars"

definition lst :: "('a,'b) seq \<Rightarrow> 'a"
 where "lst ss = (if snd ss = [] then fst ss else snd (last (snd ss)))"

text \<open>results on seqs\<close>
lemma seq_tail1: assumes seq: "(s,x#xs) \<in> seq lars"
shows "(snd x,xs) \<in> seq lars" and "(s,fst x,snd x) \<in> lars" and "lst (s,x#xs) = lst (snd x,xs)"
proof -
 show "(snd x,xs)\<in> seq lars" using assms by (cases) auto
next
 show "(s,fst x,snd x) \<in> lars"  using assms by (cases) auto
next
 show "lst (s,x#xs) = lst (snd x,xs)" using assms unfolding lst_def by (cases) auto
qed

lemma seq_chop: assumes "(s,ss@ts) \<in> seq ars" shows "(s,ss) \<in> seq ars" "(lst(s,ss),ts) \<in> seq ars" proof -
 show "(s,ss) \<in> seq ars" using assms proof (induct ss arbitrary: s)
  case Nil show ?case using seq.intros(1) by fast
 next
  case (Cons x xs) hence k:"(s,x#(xs@ts)) \<in> seq ars" by auto
  from Cons have "(snd x,xs) \<in> seq ars" using seq_tail1(1) unfolding append.simps by fast
  thus ?case using seq.intros(2)[OF seq_tail1(2)[OF k]] by auto
 qed
next
 show "(lst(s,ss),ts) \<in> seq ars" using assms proof (induct ss arbitrary:s)
  case Nil thus ?case unfolding lst_def by auto
 next
  case (Cons x xs)
  hence "(lst (snd x,xs),ts) \<in> seq ars" using seq_tail1(1) unfolding append.simps by fast
  thus ?case unfolding lst_def by auto
 qed
qed

lemma seq_concat_helper:
assumes "(s,ls) \<in> seq ars" and "ss2 \<in> seq ars" and "lst (s,ls) = fst ss2"
shows "(s,ls@snd ss2) \<in> seq ars \<and> (lst (s,ls@snd ss2) = lst ss2)"
using assms proof (induct ls arbitrary: s ss2 rule:list.induct)
 case Nil thus ?case unfolding lst_def by auto
 next
 case (Cons x xs)
 hence "(snd x,xs) \<in> seq ars" and mem:"(s,fst x,snd x) \<in> ars" and "lst (snd x,xs) = fst ss2"
  using seq_tail1[OF Cons(2)] Cons(4) by auto
 thus ?case using Cons seq.intros(2)[OF mem] unfolding lst_def by auto
qed

lemma seq_concat:
 assumes "ss1 \<in> seq ars" and "ss2 \<in> seq ars" and "lst ss1 = fst ss2"
 shows "(fst ss1,snd ss1@snd ss2) \<in> seq ars" and "(lst (fst ss1,snd ss1@snd ss2) = lst ss2)"
 proof -
  show "(fst ss1,snd ss1@snd ss2) \<in> seq ars" using seq_concat_helper assms by force
 next
  show "(lst (fst ss1,snd ss1@snd ss2) = lst ss2)"
   using assms surjective_pairing seq_concat_helper by metis
qed

text \<open>diagrams\<close>

definition diagram :: "('a,'b) lars \<Rightarrow> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<Rightarrow> bool"
 where "diagram ars d = (let (\<tau>,\<sigma>,\<sigma>',\<tau>') = d in {\<sigma>,\<tau>,\<sigma>',\<tau>'} \<subseteq> seq ars \<and>
   fst \<sigma> = fst \<tau> \<and> lst \<sigma> = fst \<tau>' \<and> lst \<tau> = fst \<sigma>' \<and> lst \<sigma>' = lst \<tau>')"

definition labels :: "('a,'b) seq \<Rightarrow> 'b list"
 where "labels ss = map fst (snd ss)"

definition D2 :: "'b rel \<Rightarrow> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<Rightarrow> bool"
 where "D2 r d = (let (\<tau>,\<sigma>,\<sigma>',\<tau>') = d in D r (labels \<tau>) (labels \<sigma>) (labels \<sigma>') (labels \<tau>'))"

lemma lemma3_5_d: assumes "diagram ars (\<tau>,\<sigma>,\<sigma>',\<tau>')" and "diagram ars (\<upsilon>,\<sigma>',\<sigma>'',\<upsilon>')"
shows "diagram ars ((fst \<tau>,snd \<tau>@snd \<upsilon>),\<sigma>,\<sigma>'',(fst \<tau>'),snd \<tau>'@snd \<upsilon>')" proof -
 from assms have tau: "\<tau> \<in> seq ars" and upsilon: "\<upsilon> \<in> seq ars" and o: "lst \<tau> = fst \<upsilon>"
            and tau': "\<tau>' \<in> seq ars" and upsilon': "\<upsilon>' \<in> seq ars" and l: "lst \<tau>' = fst \<upsilon>'"
  unfolding diagram_def by auto
show ?thesis using assms seq_concat[OF tau' upsilon' l] seq_concat[OF tau upsilon o] unfolding diagram_def by auto
qed

lemma lemma3_5_d_v: assumes "diagram ars (\<tau>,\<sigma>,\<sigma>',\<tau>')" and "diagram ars (\<tau>',\<upsilon>,\<upsilon>',\<tau>'')"
shows "diagram ars (\<tau>,(fst \<sigma>,snd \<sigma>@snd \<upsilon>),(fst \<sigma>',snd \<sigma>'@snd \<upsilon>'),\<tau>'')" proof -
 from assms have d1: "diagram ars (\<sigma>,\<tau>,\<tau>',\<sigma>')" and d2: "diagram ars (\<upsilon>,\<tau>',\<tau>'',\<upsilon>')" unfolding diagram_def by auto
 show ?thesis using lemma3_5_d[OF d1 d2] unfolding diagram_def by auto
qed

lemma lemma3_5': assumes "trans r" and "irrefl r" and "D2 r (\<tau>,\<sigma>,\<sigma>',\<tau>')" and "D2 r (\<upsilon>,\<sigma>',\<sigma>'',\<upsilon>')"
shows "D2 r ((fst \<tau>,snd \<tau>@snd \<upsilon>),\<sigma>,\<sigma>'',(fst \<tau>'),snd \<tau>'@snd \<upsilon>')"
 using assms lemma3_5[OF assms(1,2)] unfolding labels_def D2_def by auto

lemma lemma3_5'_v: assumes "trans r" and "irrefl r" and "D2 r (\<tau>,\<sigma>,\<sigma>',\<tau>')" and "D2 r (\<tau>',\<upsilon>,\<upsilon>',\<tau>'')"
shows "D2 r (\<tau>, (fst \<sigma>,snd \<sigma>@snd \<upsilon>),(fst \<sigma>',snd \<sigma>'@snd \<upsilon>'),\<tau>'')" proof -
 from assms(3,4) have D1:"D2 r (\<sigma>,\<tau>,\<tau>',\<sigma>')" and D2: "D2 r (\<upsilon>,\<tau>',\<tau>'',\<upsilon>')"
  unfolding D2_def using mirror_D[OF assms(1,2)] by auto
 show ?thesis using lemma3_5'[OF assms(1,2) D1 D2] mirror_D[OF assms(1,2)] unfolding D2_def by auto
qed

lemma trivial_diagram: assumes "\<sigma> \<in> seq ars" shows "diagram ars (\<sigma>,(fst \<sigma>,[]),(lst \<sigma>,[]),\<sigma>)"
 using assms seq.intros(1) unfolding diagram_def Let_def lst_def by auto

lemma trivial_D2: assumes "\<sigma> \<in> seq ars" shows "D2 r (\<sigma>,(fst \<sigma>,[]),(lst \<sigma>,[]),\<sigma>)"
 using assms unfolding D2_def D_def labels_def using mul_eq_reflexive by auto

(* lift to combined concept *)
definition DD :: "('a,'b) lars \<Rightarrow> 'b rel \<Rightarrow> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<Rightarrow> bool"
 where "DD ars r d = (diagram ars d \<and> D2 r d)"

lemma lemma3_5_DD: assumes "trans r" and "irrefl r" and "DD ars r (\<tau>,\<sigma>,\<sigma>',\<tau>')" and "DD ars r (\<upsilon>,\<sigma>',\<sigma>'',\<upsilon>')"
shows "DD ars r ((fst \<tau>,snd \<tau>@snd \<upsilon>),\<sigma>,\<sigma>'',(fst \<tau>'),snd \<tau>'@snd \<upsilon>')"
  using assms lemma3_5_d lemma3_5'[OF assms(1,2)] unfolding DD_def by fast

lemma lemma3_5_DD_v: assumes "trans r" and "irrefl r" and "DD ars r (\<tau>,\<sigma>,\<sigma>',\<tau>')" and "DD ars r (\<tau>',\<upsilon>,\<upsilon>',\<tau>'')"
shows "DD ars r (\<tau>, (fst \<sigma>,snd \<sigma>@snd \<upsilon>),(fst \<sigma>',snd \<sigma>'@snd \<upsilon>'),\<tau>'')"
  using assms lemma3_5_d_v lemma3_5'_v unfolding DD_def by fast

lemma trivial_DD: assumes "\<sigma> \<in> seq ars" shows "DD ars r (\<sigma>,(fst \<sigma>,[]),(lst \<sigma>,[]),\<sigma>)"
 using assms trivial_diagram trivial_D2 unfolding DD_def by fast

lemma mirror_DD: assumes "trans r" and "irrefl r" and "DD ars r (\<tau>,\<sigma>,\<sigma>',\<tau>')" shows "DD ars r (\<sigma>,\<tau>,\<tau>',\<sigma>')"
 using assms mirror_D unfolding DD_def D2_def diagram_def by auto

text \<open>well-foundedness of rel r\<close>

definition measure :: "'b rel \<Rightarrow> ('a,'b) seq \<times> ('a,'b) seq \<Rightarrow> 'b multiset"
 where "measure r P = r|labels (fst P)| + r|labels (snd P)|"

definition pex :: "'b rel \<Rightarrow> (('a,'b) seq \<times> ('a,'b) seq) rel"
 where "pex r = {(P1,P2). (measure r P1,measure r P2) \<in> mul r}"

lemma wfi: assumes "relr = pex r" and "\<not> wf (relr)" shows "\<not> wf (mul r)" proof -
 have "\<not> SN ((relr)\<inverse>)" using assms unfolding SN_iff_wf converse_converse by auto
 from this obtain s where "\<forall>i. (s i, s (Suc i)) \<in> relr\<inverse>" unfolding SN_def SN_on_def by auto
 hence fact:"\<forall>i. (measure r (s i), measure r (s (Suc i))) \<in> (mul r)\<inverse>" unfolding assms(1) pex_def by auto
 have "\<not> SN ((mul r)\<inverse>)" using chain_imp_not_SN_on[OF fact] unfolding SN_on_def by auto
 thus ?thesis unfolding SN_iff_wf converse_converse by auto
qed

lemma wf: assumes "trans r" and "wf r" shows "wf (pex r)" using wf_mul[OF assms] wfi by auto

text \<open>main result\<close>

definition peak :: "('a,'b) lars \<Rightarrow> ('a,'b) seq \<times> ('a,'b) seq \<Rightarrow> bool"
 where "peak ars p = (let (\<tau>,\<sigma>) = p in {\<tau>,\<sigma>} \<subseteq> seq ars \<and> fst \<tau> = fst \<sigma>)"

definition local_peak :: "('a,'b) lars \<Rightarrow> ('a,'b) seq \<times> ('a,'b) seq \<Rightarrow> bool"
 where "local_peak ars p = (let (\<tau>,\<sigma>) = p in peak ars p \<and> length (snd \<tau>) = 1 \<and> length (snd \<sigma>) = 1)"

text \<open>proof of Theorem 3.7\<close>
lemma LD_imp_D: assumes "trans r" and "wf r" and "\<forall>P. (local_peak ars P \<longrightarrow> (\<exists> \<sigma>' \<tau>'. DD ars r (fst P,snd P,\<sigma>',\<tau>')))"
and "peak ars P" shows "(\<exists> \<sigma>' \<tau>'. DD ars r (fst P,snd P,\<sigma>',\<tau>'))" proof -
 have i: "irrefl r" using assms(1,2) acyclic_irrefl trancl_id wf_acyclic by metis
 have wf: "wf (pex r)" using wf[OF assms(1,2)] .
 show ?thesis using assms(4) proof (induct rule:wf_induct_rule[OF wf])
  case (1 P)
  obtain s \<tau> \<sigma> where decompose:"P = (\<tau>,\<sigma>)" and tau:"\<tau> \<in> seq ars" and sigma:"\<sigma> \<in> seq ars"
   and tau_s: "fst \<tau> = s" and sigma_s: "fst \<sigma> = s" using 1 unfolding peak_def by auto
  show ?case proof (cases "snd \<tau>")
   case Nil from mirror_DD[OF assms(1) i trivial_DD[OF sigma]]
   show ?thesis using tau_s sigma_s Nil surjective_pairing unfolding decompose fst_conv snd_conv DD_def by metis
  next
   case (Cons \<beta>_step \<upsilon>_step)
   hence tau_dec: "\<tau> = (s,[\<beta>_step]@\<upsilon>_step)" apply auto using tau_s surjective_pairing by metis
   hence tau2:" (s,[\<beta>_step]@\<upsilon>_step) \<in> seq ars" using tau by auto
   show ?thesis proof (cases "snd \<sigma>")
    case Nil from trivial_DD[OF tau]
    show ?thesis using tau_s sigma_s Nil surjective_pairing unfolding decompose fst_conv snd_conv DD_def by metis
   next
    case (Cons \<alpha>_step \<rho>_step)
    hence sigma_dec: "\<sigma> = (s,[\<alpha>_step]@\<rho>_step)" apply auto using sigma_s surjective_pairing by metis
    hence sigma2:"(s,[\<alpha>_step]@\<rho>_step) \<in> seq ars" using sigma by auto

    have alpha:"(s,[\<alpha>_step]) \<in> seq ars" (is "?\<alpha> \<in> _")
     and rho: "(lst (s,[\<alpha>_step]),\<rho>_step) \<in> seq ars" (is "?\<rho> \<in> _") using seq_chop[OF sigma2] by auto
    have beta:"(s,[\<beta>_step]) \<in> seq ars" (is "?\<beta> \<in> _")
     and upsilon: "(lst (s,[\<beta>_step]),\<upsilon>_step) \<in> seq ars" (is "?\<upsilon> \<in> _") using seq_chop[OF tau2] by auto
    have "local_peak ars (?\<beta>,?\<alpha>)" using alpha beta unfolding local_peak_def peak_def by auto
    from this obtain \<kappa> \<mu> where D:"DD ars r (?\<beta>,?\<alpha>,\<kappa>,\<mu>)" using assms(3) apply auto by metis
    hence kappa: "\<kappa>\<in>seq ars" and mu: "\<mu>\<in>seq ars" unfolding DD_def diagram_def by auto
    have P_IH1: " peak ars (?\<upsilon>,\<kappa>)" using upsilon kappa D unfolding DD_def diagram_def peak_def by auto
    have beta_ne: "labels ?\<beta> \<noteq> []" unfolding labels_def by auto
    have dec: "D r (labels ?\<beta>) (labels ?\<alpha>) (labels \<kappa>) (labels \<mu>)" using D unfolding DD_def D2_def by auto
    have x1:"((?\<upsilon>,\<kappa>), (\<tau>,?\<alpha>)) \<in> pex r" using lemma3_6[OF assms(1) beta_ne dec]
      unfolding pex_def measure_def decompose labels_def tau_dec by (simp add: add.commute)
    have "(lexmax r (labels \<tau>) + lexmax r (labels (?\<alpha>)), lexmax r (labels \<tau>) + lexmax r (labels \<sigma>)) \<in> mul_eq r" (is "(?l,?r) \<in> _")
     unfolding sigma_dec labels_def snd_conv list.map lexmax.simps diff_from_empty
     using assms(1) by (simp add: lemma2_6_2_a)
    hence "((?\<upsilon>,\<kappa>),P) \<in> pex r" using x1 unfolding sigma_s pex_def measure_def decompose using mul_and_mul_eq_imp_mul[OF assms(1)] by auto
    from this obtain \<kappa>' \<upsilon>' where IH1: "DD ars r (?\<upsilon>,\<kappa>,\<kappa>',\<upsilon>')" using 1(1)[OF _ P_IH1] unfolding decompose by auto
    hence kappa':"\<kappa>'\<in>seq ars" and upsilon': "\<upsilon>'\<in>seq ars" using D unfolding DD_def diagram_def by auto
    have tau': "(fst \<mu>,snd \<mu>@(snd \<upsilon>')) \<in> seq ars" (is "?\<tau>' \<in> _") using seq_concat(1)[OF mu upsilon'] D IH1 unfolding DD_def diagram_def by auto
    have DIH1: "DD ars r (\<tau>,?\<alpha>,\<kappa>',?\<tau>')" using lemma3_5_DD[OF assms(1) i D IH1] tau_dec by auto
    hence dec_dih1: "D r (labels \<tau>) (labels ?\<alpha>) (labels \<kappa>') (labels ?\<tau>')" using DIH1 unfolding DD_def D2_def by simp

    have P_IH2: "peak ars (?\<tau>',?\<rho>)" using tau' rho D unfolding DD_def diagram_def peak_def by auto
    have alpha_ne: "labels ?\<alpha> \<noteq> []" unfolding labels_def by simp
    have "((?\<tau>',?\<rho>),P) \<in> pex r" using lemma3_6_v[OF assms(1) i alpha_ne dec_dih1] unfolding pex_def measure_def decompose labels_def sigma_dec by auto
    from this obtain \<rho>' \<tau>'' where IH2: "DD ars r (?\<tau>',?\<rho>,\<rho>',\<tau>'')" using 1(1)[OF _ P_IH2] by auto
    show ?thesis using lemma3_5_DD_v[OF assms(1) i DIH1 IH2] unfolding decompose fst_conv snd_conv sigma_dec by fast
   qed
  qed
 qed
qed

text \<open>CR with unlabeling\<close>
definition unlabel :: "('a,'b) lars \<Rightarrow> 'a rel"
 where "unlabel ars = {(a,c). \<exists>b. (a,b,c) \<in> ars}"

lemma step_imp_seq: assumes "(a,b) \<in> (unlabel ars)"
shows "\<exists>ss \<in> seq ars. fst ss = a \<and> lst ss = b" proof -
 obtain \<alpha> where step:"(a,\<alpha>,b) \<in> ars" using assms unfolding unlabel_def by auto
 hence ss: "(a,[(\<alpha>,b)]) \<in> seq ars" (is "?ss \<in> _") using seq.intros by fast
 have "fst ?ss = a" and "lst ?ss = b" unfolding lst_def by auto
 thus ?thesis using ss unfolding lst_def by fast
qed

lemma steps_imp_seq: assumes "(a,b) \<in> (unlabel ars)^*"
shows "\<exists>ss \<in> seq ars. fst ss = a \<and> lst ss = b" using assms(1) proof
 fix n assume A: "(a,b) \<in> (unlabel ars)^^n" thus ?thesis proof (induct n arbitrary: a b ars)
 case 0 hence eq: "a = b" by auto
   have "(a,[]) \<in> seq ars" using seq.intros(1) by fast
  thus ?case using fst_eqD snd_conv lst_def eq by metis
 next
 case (Suc m)
  obtain c where steps: "(a,c) \<in> (unlabel ars)^^m" and step: "(c,b) \<in> (unlabel ars)" using Suc by auto
  obtain ss ts where ss1: "ss \<in> seq ars" and ss2:"fst ss = a"
   and ts1: "ts \<in> seq ars" and ts3:"lst ts = b" and eq: "lst ss = fst ts"
   using Suc steps step_imp_seq[OF step] by metis
 show ?case using seq_concat[OF ss1 ts1 eq] unfolding ss2 ts3 by force
qed
qed

lemma step_imp_unlabeled_step: assumes "(a,b,c) \<in> ars" shows "(a,c) \<in> (unlabel ars)"
 using assms unfolding unlabel_def by auto

lemma seq_imp_steps:
assumes "ss \<in> seq ars" and "fst ss = a" and "lst ss = b" shows "(a,b) \<in> (unlabel ars)^*" proof -
 from assms surjective_pairing obtain ls where "(a,ls) \<in> seq (ars)" and "lst (a,ls) = b" by metis
 thus ?thesis proof (induct ls arbitrary: a b rule:list.induct)
  case Nil thus ?case unfolding lst_def by auto
 next
  case (Cons x xs)
  have fst:"(a,fst x,snd x) \<in> ars" using Cons seq_tail1(2) surjective_pairing by metis
  have "(snd x,b) \<in> (unlabel ars)^*" using Cons seq_tail1(1,3) by metis
  thus ?case using step_imp_unlabeled_step[OF fst] by auto
 qed
qed

lemma seq_vs_steps: shows "(a,b) \<in> (unlabel ars)^* = (\<exists>ss. fst ss = a \<and> lst ss = b \<and> ss \<in> seq ars)"
 using seq_imp_steps steps_imp_seq by metis

lemma D_imp_CR: assumes "\<forall>P. (peak ars P \<longrightarrow> (\<exists> \<sigma>' \<tau>'. DD ars r (fst P,snd P,\<sigma>',\<tau>')))" shows "CR (unlabel ars)" proof
 fix a b c assume A: "(a,b) \<in> (unlabel ars)^*" and B: "(a,c) \<in> (unlabel ars)^*" show "(b,c) \<in> (unlabel ars)\<^sup>\<down>" proof -
  obtain ss1 ss2 where " peak ars (ss1,ss2)" and b: "lst ss1 = b" and c: "lst ss2 = c"
   unfolding peak_def using A B unfolding seq_vs_steps by auto
  from this obtain ss3 ss4 where dia: "diagram ars (ss1,ss2,ss3,ss4)" using assms(1) unfolding DD_def apply auto using surjective_pairing by metis
  from dia obtain d where ss3: "ss3 \<in> seq ars" and ss4: "ss4 \<in> seq ars"
   and ss3_1: "fst ss3 = b" and ss3_2: "lst ss3 = d" and ss4_1: "fst ss4 = c" and ss4_2:"lst ss4 = d"
   using b c unfolding diagram_def by auto
  show ?thesis using seq_imp_steps[OF ss3 ss3_1 ss3_2] seq_imp_steps[OF ss4 ss4_1 ss4_2] by auto
 qed
qed

definition LD :: "'b set \<Rightarrow> 'a rel \<Rightarrow> bool"
 where "LD L ars = (\<exists> (r:: ('b rel)) (lrs::('a,'b) lars). (ars = unlabel lrs) \<and> trans r \<and> wf r \<and> (\<forall>P. (local_peak lrs P \<longrightarrow> (\<exists> \<sigma>' \<tau>'. (DD lrs r (fst P,snd P,\<sigma>',\<tau>'))))))"

lemma sound: assumes "LD L ars" shows "CR ars"
 using assms LD_imp_D D_imp_CR unfolding LD_def by metis

subsubsection \<open>Application: Newman's Lemma\<close>
lemma measure:
assumes lab_eq: "lrs = {(a,c,b). c = a \<and> (a,b) \<in> ars}" and "(s,(\<alpha>,t) # ss) \<in> seq lrs"
shows "set (labels (t,ss)) \<subseteq> ds ((ars^+)\<inverse>) {\<alpha>}" using assms(2) proof (induct ss arbitrary: s \<alpha> t )
 case Nil thus ?case unfolding labels_def by auto
next
 case (Cons x xs)
 from this obtain \<beta> u where x:"x = (\<beta>,u)" using surjective_pairing by metis
 have t: "trans ((ars^+)\<inverse>)" by (metis trans_converse trans_trancl)
 from Cons(1) x have s0: "(s, \<alpha>, t) \<in> lrs" and cs:"(t,(\<beta>,u)#xs) \<in> seq lrs" using Cons.prems seq_tail1(1) snd_conv fst_conv seq_tail1(2) by auto
 have ih: "set (labels (u, xs)) \<subseteq> ds ((ars^+)\<inverse>) {\<beta>}" using Cons(1)[OF cs] by auto
 have key: "{\<beta>} \<subseteq> ds ((ars^+)\<inverse>) {\<alpha>}" using s0 cs seq_tail1(2)[OF cs] unfolding ds_def lab_eq by auto
 show ?case using ih subset_imp_ds_subset[OF t key] key unfolding x labels_def by auto
qed

lemma newman: assumes "WCR ars" and "SN ars" shows "CR ars"  proof -
 from assms obtain L where "L =  {a . \<exists> b. (a,b) \<in> ars}" by auto
 from assms obtain lrs where lab_eq: "(lrs  = {(a,c,b). c = a \<and> (a,b) \<in> ars})" by auto

 have lab: "ars = unlabel lrs" unfolding unlabel_def lab_eq by auto
 have t: "trans ((ars^+)\<inverse>)" using trans_converse trans_trancl by auto
 have w: "wf ((ars^+)\<inverse>)" using assms(2) wf_trancl trancl_converse unfolding SN_iff_wf by metis
 have ps: "\<forall>P. (local_peak lrs P --> (\<exists> \<sigma>' \<tau>'. DD lrs ((ars^+)\<inverse>) (fst P,snd P,\<sigma>',\<tau>')))" proof
  fix P show "local_peak lrs P --> (\<exists> \<sigma>' \<tau>'. DD lrs ((ars^+)\<inverse>) (fst P,snd P,\<sigma>',\<tau>'))" proof
   assume A: "local_peak lrs P" show "(\<exists> \<sigma>' \<tau>'. DD lrs ((ars^+)\<inverse>) (fst P,snd P,\<sigma>',\<tau>'))" (is "?DD") proof -
    from lab_eq have lab: "ars = unlabel lrs" unfolding unlabel_def by auto
    from A obtain \<tau> \<sigma> where ts: "{\<tau>,\<sigma>} \<subseteq> seq lrs" and l1: "length (snd \<tau>) = 1" and l2: "length (snd \<sigma>) = 1" and P: "P = (\<tau>,\<sigma>)"
     and p: "fst \<tau> = fst \<sigma>" unfolding local_peak_def peak_def by auto

    from l1 obtain \<beta> b where 1: "snd \<tau> = [(\<beta>,b)]" by(auto simp add: length_Suc_conv)
    from this obtain a where tau: "\<tau> = (a,[(\<beta>,b)])" by (metis surjective_pairing)
    hence alb: "(a,\<beta>,b) \<in> lrs" using ts by (metis fst_conv insert_subset seq_tail1(2) snd_conv)
    have ab: "(a,b) \<in> ars" and a_eq: "a = \<beta>" using alb unfolding lab_eq by auto

    from l2 obtain \<alpha> c where 2: "snd \<sigma> = [(\<alpha>,c)]" by(auto simp add: length_Suc_conv)
    hence sigma: "\<sigma> = (a,[(\<alpha>,c)])" using ts by (metis fst_conv p prod.collapse tau)
    hence alc: "(a,\<alpha>,c) \<in> lrs" using ts by (metis fst_conv insert_subset seq_tail1(2) snd_conv)
    hence ac: "(a,c) \<in> ars" and a_eq: "a = \<alpha>" using alb unfolding lab_eq by auto

    from tau sigma have fl: "fst \<tau> = a \<and> fst \<sigma> = a \<and> lst \<tau> = b \<and> lst \<sigma> = c" unfolding lst_def by auto
    from ab ac obtain d where "(b,d) \<in> ars^*" and "(c,d) \<in> ars^*" using assms(1) by auto
    from this obtain \<sigma>' \<tau>' where sigma': "\<sigma>' \<in> seq lrs" and sigma'1: "fst \<sigma>' = b" and "lst \<sigma>' = d"
                           and  tau':"\<tau>' \<in> seq lrs" and "fst \<tau>' = c" and "lst \<tau>' = d" using steps_imp_seq unfolding lab by metis
    hence d:"diagram lrs (fst P, snd P, \<sigma>', \<tau>')" using P A ts fl unfolding local_peak_def peak_def diagram_def by auto

    have s1:"(a,(\<beta>,b)# snd \<sigma>') \<in> seq lrs" using \<open>fst \<sigma>' = b\<close> seq.intros(2)[OF alb] sigma' by auto
    have vv: "set (labels \<sigma>') \<subseteq> ds ((ars^+)\<inverse>) {\<beta>}"  using measure[OF lab_eq s1] by (metis \<open>fst \<sigma>' = b\<close> surjective_pairing)
    have s2:"(a,(\<alpha>,c)# snd \<tau>') \<in> seq lrs" using \<open>fst \<tau>' = c\<close> seq.intros(2)[OF alc] tau' by auto
    hence ww: "set (labels \<tau>') \<subseteq> ds ((ars^+)\<inverse>) {\<alpha>}" using measure[OF lab_eq] s2 by (metis \<open>fst \<tau>' = c\<close> surjective_pairing)
    from w have i: "irrefl ((ars^+)\<inverse>)" by (metis SN_imp_acyclic acyclic_converse acyclic_irrefl assms(2) trancl_converse)
    from vv ww have ld: "LD' ((ars^+)\<inverse>) \<beta> \<alpha> (labels \<sigma>') [] [] (labels \<tau>') [] []" unfolding LD'_def LD_1'_def by auto
    have D: "D ((ars^+)\<inverse>) (labels (fst P)) (labels (snd P)) (labels \<sigma>') (labels \<tau>')" using proposition3_4[OF t i ld] unfolding P sigma tau lst_def labels_def by auto

    from d D have "DD lrs ((ars^+)\<inverse>) (fst P, snd P, \<sigma>', \<tau>')" unfolding DD_def D2_def by auto
    thus ?thesis by fast
   qed
  qed
 qed
 have "LD L ars" using lab t w ps unfolding LD_def by fast
 thus ?thesis using sound by auto
qed

subsection \<open>Conversion Version\<close>
text \<open>This section follows~\cite{vO08a}.\<close>
text \<open>auxiliary results on multisets\<close>
lemma mul_eq_add_right: "(M,M+P) \<in> mul_eq r" proof -
 have "M = M + {#}" "set_mset {#} \<subseteq> dm r P" by auto
 thus ?thesis unfolding mul_eq_def by fast
qed

lemma mul_add_right: assumes "(M,N) \<in> mul r" shows "(M,N+P) \<in> mul r" proof -
 from assms obtain I J K where "M = I + K" "N = I + J" "set_mset K \<subseteq> dm r J" "J \<noteq> {#}" unfolding mul_def by auto
 hence b: "M = I + K" "N + P = I + (J + P)" "set_mset K \<subseteq> ds r (set_mset J \<union> set_mset P)" "J+P \<noteq> {#}" unfolding dm_def lemma2_6_1_set using union_assoc by auto
 hence "set_mset K \<subseteq> ds r (set_mset (J+P ))" by auto
 thus ?thesis using b unfolding mul_def unfolding dm_def by fast
qed

lemma mul_eq_and_ds_imp_ds:
assumes t: "trans r" and "(M,N) \<in> mul_eq r" and "set_mset N \<subseteq> ds r S"
shows "set_mset M \<subseteq> ds r S" proof -
 from assms obtain I J K where a: "M = I + K" and "N = I + J" and c: "set_mset K \<subseteq> dm r J" unfolding mul_eq_def by auto
 hence k1:"set_mset I \<subseteq> ds r S" "set_mset J \<subseteq> ds r S" using assms by auto
 hence "ds r (set_mset J) \<subseteq> ds r S"  using subset_imp_ds_subset[OF t] by auto
 thus ?thesis using k1 a c unfolding dm_def by auto
qed

lemma lemma2_6_2_set: assumes "S \<subseteq> T" shows "ds r S \<subseteq> ds r T" using assms unfolding ds_def by auto

lemma leq_imp_subseteq: assumes "M \<subseteq># N" shows "set_mset M \<subseteq> set_mset N" using assms mset_subset_eqD by auto

lemma mul_add_mul_eq_imp_mul: assumes "(M,N) \<in> mul r" and "(P,Q) \<in> mul_eq r" shows "(M+P,N+Q) \<in> mul r" proof -
 from assms(1) obtain I J K where a:"M = I + K" "N = I + J" "set_mset K \<subseteq> dm r J" "J \<noteq> {#}" unfolding mul_def by auto
 from assms(2) obtain I2 J2 K2 where b:"P = I2 + K2" "Q = I2 + J2" "set_mset K2 \<subseteq> dm r J2" unfolding mul_eq_def by auto
 have "M + P = (I + I2) + (K + K2)" using a b union_commute union_assoc by metis
 moreover have "N + Q = (I + I2) + (J + J2)" using a b union_commute union_assoc by metis
 moreover have "set_mset (K + K2) \<subseteq> dm r (J + J2)"  using a b unfolding lemma2_6_1_multiset by auto
 ultimately show ?thesis using a b unfolding mul_def by fast
qed

text \<open>labeled conversion\<close>
type_synonym ('a,'b) conv = "('a \<times> ((bool \<times> 'b \<times> 'a) list))"

inductive_set conv :: "('a,'b) lars \<Rightarrow> ('a,'b) conv set" for ars
where "(a,[]) \<in> conv ars"
    | "(a,\<alpha>,b) \<in> ars \<Longrightarrow> (b,ss) \<in> conv ars \<Longrightarrow> (a,(True,\<alpha>,b) # ss) \<in> conv ars"
    | "(b,\<alpha>,a) \<in> ars \<Longrightarrow> (b,ss) \<in> conv ars \<Longrightarrow> (a,(False,\<alpha>,b) # ss) \<in> conv ars"

definition labels_conv :: "('a,'b) conv \<Rightarrow> 'b list"
 where "labels_conv c = map (\<lambda>q. (fst (snd q))) (snd c)"

definition measure_conv :: "'b rel \<Rightarrow> ('a,'b) conv \<Rightarrow> 'b multiset"
 where "measure_conv r c = lexmax r (labels_conv c)"

fun lst_conv :: "('a,'b) conv \<Rightarrow> 'a"
  where "lst_conv (s,[]) = s"
 | "lst_conv (s,(d,\<alpha>,t) # ss) = lst_conv (t,ss)"

definition local_diagram1 :: "('a,'b) lars \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> bool"
 where "local_diagram1 ars \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 =
  (local_peak ars (\<beta>,\<alpha>) \<and> {\<sigma>1,\<sigma>2,\<sigma>3} \<subseteq> seq ars \<and> lst \<beta> = fst \<sigma>1 \<and> lst \<sigma>1 = fst \<sigma>2 \<and> lst \<sigma>2 = fst \<sigma>3)"

definition LDD1 :: "('a,'b) lars \<Rightarrow> 'b rel \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> bool"
 where "LDD1 ars r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 =  (local_diagram1 ars \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 \<and>
  LD_1' r (hd (labels \<beta>)) (hd (labels \<alpha>)) (labels \<sigma>1) (labels \<sigma>2) (labels \<sigma>3))"

definition LDD :: "('a,'b) lars \<Rightarrow> 'b rel \<Rightarrow> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<Rightarrow> bool"
 where "LDD ars r d = (let (\<beta>,\<alpha>,\<sigma>1,\<sigma>2,\<sigma>3,\<tau>1,\<tau>2,\<tau>3) = d in LDD1 ars r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 \<and> LDD1 ars r \<alpha> \<beta> \<tau>1 \<tau>2 \<tau>3 \<and> lst \<sigma>3 = lst \<tau>3)"

definition local_triangle1 :: "('a,'b) lars \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) conv \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) conv \<Rightarrow> bool"
 where "local_triangle1 ars \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 =
  (local_peak ars (\<beta>,\<alpha>) \<and> \<sigma>2 \<in> seq ars \<and> {\<sigma>1,\<sigma>3} \<subseteq> conv ars \<and> lst \<beta> = fst \<sigma>1 \<and> lst_conv \<sigma>1 = fst \<sigma>2 \<and> lst \<sigma>2 = fst \<sigma>3)"

definition LT1 :: "('a,'b) lars \<Rightarrow> 'b rel \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) conv \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) conv \<Rightarrow> bool"
 where "LT1 ars r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 = (local_triangle1 ars \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 \<and>
  LD_1' r (hd (labels \<beta>)) (hd (labels \<alpha>)) (labels_conv \<sigma>1) (labels \<sigma>2) (labels_conv \<sigma>3))"

definition LT :: "('a,'b) lars \<Rightarrow> 'b rel \<Rightarrow> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) conv \<times> ('a,'b) seq \<times> ('a,'b) conv \<times> ('a,'b) conv \<times> ('a,'b) seq \<times> ('a,'b) conv \<Rightarrow> bool"
 where "LT ars r t = (let (\<beta>,\<alpha>,\<sigma>1,\<sigma>2,\<sigma>3,\<tau>1,\<tau>2,\<tau>3) = t in LT1 ars r \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 \<and> LT1 ars r \<alpha> \<beta> \<tau>1 \<tau>2 \<tau>3 \<and> lst_conv \<sigma>3 = lst_conv \<tau>3)"

lemma conv_tail1: assumes conv: "(s,(d,\<alpha>,t)#xs) \<in> conv ars"
shows "(t,xs) \<in> conv ars" and "d \<Longrightarrow> (s,\<alpha>,t) \<in> ars" and "\<not>d \<Longrightarrow> (t,\<alpha>,s) \<in> ars" and "lst_conv (s,(d,\<alpha>,t)#xs) = lst_conv (t,xs)" proof -
 show "(t,xs) \<in> conv ars" using assms by (cases) auto
 show "d \<Longrightarrow> (s,\<alpha>,t) \<in> ars" using assms by (cases) auto
 show "\<not>d \<Longrightarrow> (t,\<alpha>,s) \<in> ars" using assms by (cases) auto
 show "lst_conv (s,(d,\<alpha>,t)#xs) = lst_conv (t,xs)" unfolding lst_conv.simps by auto
qed

lemma conv_chop: assumes "(s,ss1@ss2) \<in> conv ars" shows "(s,ss1) \<in> conv ars" "(lst_conv (s,ss1),ss2) \<in> conv ars" proof -
 show "(s,ss1) \<in> conv ars" using assms proof (induct ss1 arbitrary: s)
  case Nil thus ?case using conv.intros by fast
 next
  case (Cons t' ts) from this obtain d \<alpha> t where dec: "t' = (d,\<alpha>,t)" using prod_cases3 by metis
  from Cons have "(s, t' # ts @ ss2) \<in> conv ars" by auto
  hence "(t, ts @ ss2) \<in> conv ars" and d1: "d \<Longrightarrow> (s,\<alpha>,t) \<in> ars" and d2:"\<not>d \<Longrightarrow> (t,\<alpha>,s) \<in> ars" using conv_tail1(1-3) unfolding dec by auto
  hence "(t, ts) \<in> conv ars" using Cons by auto
  thus ?case unfolding dec using Cons conv.intros d1 d2 by (cases d) auto
 qed
 show "(lst_conv (s,ss1),ss2) \<in> conv ars" using assms proof (induct ss1 arbitrary:s)
  case Nil thus ?case using conv.intros unfolding last.simps by auto
 next
  case (Cons t' ts) from this obtain d \<alpha> t where dec: "t' = (d,\<alpha>,t)" using prod_cases3 by metis
  from Cons have "(s, t' # ts @ ss2) \<in> conv ars" by auto
  hence "(snd (snd t'), ts @ ss2) \<in> conv ars" using conv_tail1(1) unfolding dec by auto
  thus ?case using Cons(1) unfolding dec last.simps by auto
 qed
qed

lemma conv_concat_helper:
assumes "(s,ls) \<in> conv ars" and "ss2 \<in> conv ars" and "lst_conv (s,ls) = fst ss2"
shows "(s,ls@snd ss2) \<in> conv ars \<and> (lst_conv (s,ls@snd ss2) = lst_conv ss2)"
using assms proof (induct ls arbitrary: s ss2 rule:list.induct)
 case Nil thus ?case unfolding lst_def by auto
 next
 case (Cons x xs) from this obtain d \<alpha> t where dec: "x = (d,\<alpha>,t)" using prod_cases3 by metis
 hence tl: "(t,xs) \<in> conv ars" and d1:"d \<Longrightarrow> (s,\<alpha>,t) \<in> ars" and d2: "\<not>d \<Longrightarrow> (t,\<alpha>,s) \<in> ars" and lst:"lst_conv (t,xs) = fst ss2"
  using conv_tail1 Cons(2) Cons(4) by auto
 have "(t,xs@snd ss2) \<in> conv ars" and lst: "lst_conv (t,xs@snd ss2) = lst_conv ss2"  using Cons(1)[OF tl Cons(3) lst] by auto
 thus ?case using conv.intros d1 d2 unfolding dec lst_conv.simps by (cases d) auto
qed

lemma conv_concat:
 assumes "ss1 \<in> conv ars" and "ss2 \<in> conv ars" and "lst_conv ss1 = fst ss2"
 shows "(fst ss1,snd ss1@snd ss2) \<in> conv ars" and "(lst_conv (fst ss1,snd ss1@snd ss2) = lst_conv ss2)"
 proof -
  show "(fst ss1,snd ss1@snd ss2) \<in> conv ars" using conv_concat_helper assms by force
 next
  show "(lst_conv (fst ss1,snd ss1@snd ss2) = lst_conv ss2)"
   using assms surjective_pairing conv_concat_helper by metis
qed

lemma conv_concat_labels:
assumes "ss1 \<in> conv ars" and "ss2 \<in> conv ars" and "set (labels_conv ss1) \<subseteq> S" and "set (labels_conv ss2) \<subseteq> T"
shows "set (labels_conv (fst ss1,snd ss1@snd ss2)) \<subseteq> S \<union> T" using assms unfolding labels_conv_def by auto

lemma seq_decompose:
assumes "\<sigma> \<in> seq ars" and "labels \<sigma> = \<sigma>1'@\<sigma>2'"
shows "\<exists> \<sigma>1 \<sigma>2. ({\<sigma>1,\<sigma>2} \<subseteq> seq ars \<and> \<sigma> = (fst \<sigma>1,snd \<sigma>1@snd \<sigma>2) \<and> lst \<sigma>1 = fst \<sigma>2 \<and> lst \<sigma>2 = lst \<sigma> \<and> labels \<sigma>1 = \<sigma>1' \<and> labels \<sigma>2 = \<sigma>2')" proof -
 obtain s ss where \<sigma>_dec: "\<sigma> = (s,ss)" using assms(1) surjective_pairing by metis
 show ?thesis using assms unfolding \<sigma>_dec proof (induct ss arbitrary: s \<sigma>1' \<sigma>2' rule:list.induct)
 case Nil thus ?case unfolding labels_def lst_def by auto
next
 case (Cons x xs)
  have step: "(s,x) \<in> ars" and x:"(snd x,xs) \<in> seq ars" using seq_tail1[OF Cons(2)] surjective_pairing by auto
  hence steps: "(s,[x]) \<in> seq ars" by (metis Cons(2) append_Cons append_Nil seq_chop(1))
  from Cons(3) have a:"fst x#labels (snd x,xs) = \<sigma>1'@\<sigma>2'" unfolding labels_def snd_conv by auto
  show ?case proof (cases "\<sigma>1'=[]")
   case True
   from a True obtain l ls where \<sigma>2'_dec: "\<sigma>2' = l#ls" and y1:"fst x = l" and y2:"labels (snd x,xs) = []@ls" by auto
   obtain \<sigma>1 \<sigma>2 where ih: "\<sigma>1 \<in> seq ars" "\<sigma>2 \<in> seq ars" "(snd x, xs) = (fst \<sigma>1, snd \<sigma>1 @ snd \<sigma>2)" "lst \<sigma>1 = fst \<sigma>2"
    "labels \<sigma>1 = []" "labels \<sigma>2 = ls" using Cons(1)[OF x y2] by blast
   hence c:"fst (snd x,xs) = fst \<sigma>1" by auto

   have 1: "\<sigma>1 = (snd x,[])" using ih unfolding labels_def apply auto by (metis surjective_pairing)
   hence 2: "snd x = fst \<sigma>1" "xs = snd \<sigma>2" using ih by auto
   have 3: "snd x = fst \<sigma>2" using ih 1 unfolding lst_def by auto
   have "\<sigma>2 = (snd x,xs)" using x 1 2 3 surjective_pairing by metis
   hence l:"lst (s, [x]) = fst \<sigma>2" unfolding lst_def by auto
   have m:"{(s,[]), (s,x# snd \<sigma>2)} \<subseteq> seq ars"  (is "{?\<sigma>1,?\<sigma>2} \<subseteq> _") using seq.intros(1) seq_concat(1)[OF steps _ l] ih by auto
   moreover have "(s, x # xs) = (fst ?\<sigma>1, snd ?\<sigma>1 @ snd ?\<sigma>2)" using m 2 by auto
   moreover have "lst ?\<sigma>1 = fst ?\<sigma>2" using m unfolding lst_def by auto
   moreover have "lst ?\<sigma>2 = lst (s,x#xs)" unfolding lst_def using 2 3 by auto
   moreover have "labels (s,[]) = \<sigma>1'" unfolding labels_def using True by auto
   moreover have "labels ?\<sigma>2 = \<sigma>2'" using ih y1 unfolding \<sigma>2'_dec labels_def by auto
   ultimately show ?thesis by metis
  next
   case False from False obtain l ls where \<sigma>1'_dec:"\<sigma>1' = l#ls" using list.exhaust by auto
   hence y1:"fst x = l" and y2:"labels (snd x,xs) = ls @ \<sigma>2'" using a by auto
   obtain \<sigma>1 \<sigma>2 where ih: "\<sigma>1 \<in> seq ars" "\<sigma>2 \<in> seq ars" "(snd x, xs) = (fst \<sigma>1, snd \<sigma>1 @ snd \<sigma>2)"
    "lst \<sigma>1 = fst \<sigma>2" "lst \<sigma>2 = lst (snd x, xs)" "labels \<sigma>1 = ls" "labels \<sigma>2 = \<sigma>2'" using  Cons(1)[OF x y2] by blast
   hence "{(s,x# snd \<sigma>1),\<sigma>2} \<subseteq> seq ars" (is "{?\<sigma>1,_} \<subseteq> seq ars") using seq_concat(1)[OF steps] ih unfolding lst_def by auto
   moreover have "(s,x#xs) = (fst ?\<sigma>1,snd ?\<sigma>1@snd \<sigma>2)" using ih by auto
   moreover have "lst ?\<sigma>1 = fst \<sigma>2" using ih unfolding lst_def by auto
   moreover have "lst \<sigma>2 = lst (s, x # xs)" using ih unfolding lst_def by auto
   moreover have "labels ?\<sigma>1 = \<sigma>1'" using ih \<sigma>1'_dec y1 unfolding labels_def by auto
   moreover have "labels \<sigma>2 = \<sigma>2'" using ih by auto
   ultimately show ?thesis by blast
  qed
 qed
qed

lemma seq_imp_conv:
assumes "(s,ss) \<in> seq ars"
shows "(s,map (\<lambda>step. (True,step)) ss) \<in> conv ars \<and>
       lst_conv (s,map (\<lambda>step.(True,step)) ss) = lst (s,ss) \<and>
       labels (s,ss) = labels_conv (s,map (\<lambda>step.(True,step)) ss)"
using assms proof (induct ss arbitrary: s rule:list.induct )
 case Nil show ?case  unfolding lst_def labels_def labels_conv_def apply auto using conv.intros by fast
next
 case (Cons t' ts) have t'_dec: "t' = (fst t',snd t')" using surjective_pairing by auto
  have step: "(s,fst t',snd t') \<in> ars" and x:"(snd t',ts) \<in> seq ars" using seq_tail1[OF Cons(2)] by auto
  have y1:"(snd t', map (Pair True) ts) \<in> conv ars" and
       y2: "lst (snd t', ts) = lst_conv (snd t', map (Pair True) ts)" and
       y3: "labels (snd t', ts) = labels_conv (snd t', map (Pair True) ts)" using Cons(1)[OF x] by auto
  have k: "(s,(True,fst t',snd t')#map (Pair True) ts) \<in> conv ars" using step y1 conv.intros by fast
  moreover have "lst (s,(fst t',snd t')#ts) = lst_conv (s, map (Pair True) ((fst t',snd t')#ts))" using y2 unfolding list.map lst_def lst_conv.simps by auto
  moreover have "labels (s,(fst t',snd t')#ts) = labels_conv (s,map (Pair True) ((fst t',snd t')#ts))" using y3 unfolding list.map labels_def labels_conv_def by auto
  ultimately show ?case by auto
qed

fun conv_mirror :: "('a,'b) conv \<Rightarrow> ('a,'b) conv"
 where "conv_mirror \<sigma> = (let (s,ss) = \<sigma> in case ss of
             [] \<Rightarrow> (s,ss)
         | x#xs \<Rightarrow> let (d,\<alpha>,t) = x in
                   (fst (conv_mirror (t,xs)),snd (conv_mirror (t,xs))@[(\<not>d,\<alpha>,s)]))"

lemma conv_mirror: assumes "\<sigma> \<in> conv ars"
shows "conv_mirror \<sigma> \<in> conv ars \<and>
      set (labels_conv (conv_mirror \<sigma>)) = set (labels_conv \<sigma>) \<and>
      fst \<sigma> = lst_conv (conv_mirror \<sigma>) \<and>
      lst_conv \<sigma> = fst (conv_mirror \<sigma>)" proof -
 from assms obtain s ss where \<sigma>_dec: "\<sigma> = (s,ss)" using surjective_pairing by metis
 show ?thesis using assms unfolding \<sigma>_dec proof (induct ss arbitrary:s rule:list.induct)
  case Nil thus ?case using conv.intros  conv_mirror.simps by auto
 next
  case (Cons t' ts) from this obtain d \<alpha> t where t'_dec: "t' = (d,\<alpha>,t)" by (metis prod_cases3)
  have 1:"(t, ts) \<in> conv ars" and 2: "d \<Longrightarrow> (s,\<alpha>,t) \<in> ars" and 3: "\<not>d \<Longrightarrow> (t,\<alpha>,s) \<in> ars"  and 4:"lst_conv (s,t'#ts) = lst_conv (t,ts)"
   using Cons(2) conv_tail1 unfolding t'_dec by auto
  have r: "(t,[(\<not>d,\<alpha>,s)]) \<in> conv ars" using 2 3 conv.intros(3)[OF _ conv.intros(1)] conv.intros(2)[OF _ conv.intros(1)] by (cases d) auto
  have "conv_mirror (s,t'#ts) \<in> conv ars" using conv_concat[OF _ r ] Cons(1)[OF 1] t'_dec by auto
  moreover have "set (labels_conv (conv_mirror (s, t' # ts))) = set (labels_conv (s, t' # ts))" using Cons(1)[OF 1] unfolding labels_conv_def t'_dec by auto
  moreover have "fst (s, t' # ts) = lst_conv (conv_mirror (s, t' # ts))" using t'_dec Cons(1)[OF 1] conv_concat(2)[OF _ r] by auto
  moreover have "lst_conv (s, t' # ts) = fst (conv_mirror (s, t' # ts))" using t'_dec 4 Cons(1)[OF 1] by auto
  ultimately show ?case by auto
 qed
qed

lemma DD_subset_helper:
assumes t:"trans r" and "(r|\<tau>@\<sigma>'|, r|\<tau>| + r|\<sigma>| ) \<in> mul_eq r" and "set_mset (r|\<tau>| + r|\<sigma>| ) \<subseteq> ds r S"
shows "set_mset r|\<sigma>'| \<subseteq> ds r S" proof -
  from assms have d: "(r|\<tau>| + r|\<sigma>'| -s dl r (\<tau>) , r|\<tau>| + r|\<sigma>| ) \<in> mul_eq r" unfolding lemma3_2_2 by auto
  from assms have assm:"set_mset (r|\<tau>| + r|\<sigma>| ) \<subseteq> ds r S" unfolding measure_def by auto
  hence tau:"ds r (set_mset r|\<tau>| ) \<subseteq> ds r S" using subset_imp_ds_subset[OF t] by auto
  have "set_mset (r|\<tau>| + (r|\<sigma>'| -s dl r \<tau>)) \<subseteq> ds r S" using mul_eq_and_ds_imp_ds[OF t d assm] by auto
  hence "set_mset (r|\<sigma>'| -s ds r (set \<tau>)) \<subseteq> ds r S" unfolding dl_def by auto
  hence "set_mset (r|\<sigma>'| -s ds r (set \<tau>)) \<union> ds r (set \<tau>) \<subseteq> ds r S" using tau by (metis t dl_def dm_def le_sup_iff lemma3_2_1)
  thus ?thesis unfolding diff_def by auto
qed

lemma DD_subset_ds:
assumes t:"trans r" and DD: "DD ars r (\<tau>,\<sigma>,\<sigma>',\<tau>')" and "set_mset (measure r (\<tau>,\<sigma>)) \<subseteq> ds r S" shows "set_mset (measure r (\<sigma>',\<tau>')) \<subseteq> ds r S" proof -
 have d1:"(r|labels \<tau> @ labels \<sigma>'|, r|labels \<tau>| + r|labels \<sigma>| ) \<in> mul_eq r" using DD unfolding DD_def D2_def D_def by auto
 have d2:"(r|labels \<sigma> @ labels \<tau>'|, r|labels \<sigma>| + r|labels \<tau>| ) \<in> mul_eq r" using DD unfolding DD_def D2_def D_def
  by (auto simp: union_commute)
 show ?thesis using DD_subset_helper[OF t d1] DD_subset_helper[OF t d2] assms(3) unfolding measure_def by auto
qed

lemma conv_imp_valley:
assumes t: "trans r"
and IH: "!!y . ((y,((s,[\<alpha>_step]@\<rho>_step),(s,[\<beta>_step]@\<upsilon>_step))) \<in> pex r \<Longrightarrow> peak ars y \<Longrightarrow> \<exists>\<sigma>' \<tau>'. DD ars r (fst y, snd y, \<sigma>', \<tau>'))" (is "!!y. ((y,?P) \<in> _ \<Longrightarrow> _ \<Longrightarrow> _)")
and "\<delta>1 \<in> conv ars"
and "set_mset (measure_conv r \<delta>1) \<subseteq> dm r M"
and "(M,{#fst \<alpha>_step,fst \<beta>_step#}) \<in> mul_eq r"
shows "\<exists> \<sigma> \<tau>. ({\<sigma>,\<tau>} \<subseteq> seq ars \<and> fst \<sigma> = fst \<delta>1 \<and> fst \<tau> = lst_conv \<delta>1 \<and> lst \<sigma> = lst \<tau> \<and> set_mset (measure r (\<sigma>,\<tau>)) \<subseteq> dm r M)" proof -
 from assms obtain s ss where sigma1: "\<delta>1 = (s,ss)" using surjective_pairing by metis
 show ?thesis using assms(3,4) unfolding sigma1 proof (induct ss arbitrary: s rule:list.induct)
  case Nil
  hence "(s,[]) \<in> seq ars" using seq.intros(1) by fast
  moreover have "set_mset (measure r ((s,[]),(s,[]))) \<subseteq> dm r M" unfolding measure_def labels_def by auto
  ultimately show ?case by auto
 next
  case (Cons t' ts) obtain d \<beta> t where dec: "t' = (d,\<beta>,t)" using surjective_pairing by metis
  hence dic: "{\<beta>} \<subseteq> ds r (set_mset M)" using Cons(3) unfolding dec measure_conv_def labels_conv_def dm_def by auto
  have one:"ds r {\<beta>} \<subseteq> dm r M " unfolding dm_def using subset_imp_ds_subset[OF t dic] by auto
  have "set_mset (measure_conv r (t,ts) -s ds r {\<beta>})  \<subseteq> dm r M" using Cons(3) unfolding measure_conv_def labels_conv_def dec by auto
  hence "set_mset (measure_conv r (t,ts)) \<subseteq> dm r M \<union> ds r {\<beta>}" unfolding set_mset_def diff_def by auto
  hence ts2: "set_mset (measure_conv r (t,ts)) \<subseteq> dm r M" using dic one by auto
  from Cons(2) have ts: "(t,ts) \<in> conv ars" unfolding dec using conv_tail1(1) by fast
  from Cons(1)[OF ts ts2] obtain \<sigma>' \<tau> where
   ih:"{\<sigma>', \<tau>} \<subseteq> seq ars \<and> fst \<sigma>' = fst (t,ts) \<and> fst \<tau> = lst_conv (t, ts) \<and> lst \<sigma>' = lst \<tau> \<and> set_mset (measure r (\<sigma>',\<tau>)) \<subseteq> dm r M" by metis
  have diff:"!!x. x \<in># r|map fst (snd \<sigma>')|-sds r {\<beta>} \<Longrightarrow> x \<in># r|map fst (snd \<sigma>')|"
    by simp
  show ?case proof (cases d)
   case True hence step:"(s,\<beta>,t) \<in> ars" using conv_tail1(2) Cons(2) unfolding dec by auto
   have "(s,(\<beta>,t)# snd \<sigma>') \<in> seq ars" (is "?\<sigma> \<in> _") using seq.intros(2)[OF step] using ih(1) by auto
   hence "{?\<sigma>,\<tau>} \<subseteq> seq ars" using ih by auto
   moreover have "(fst ?\<sigma>) = fst (s, t' # ts)" by auto
   moreover have "fst \<tau> = lst_conv (s, t' # ts)" using ih unfolding dec lst_conv.simps by auto
   moreover have "lst ?\<sigma> = lst \<tau>" by (metis \<open>(s, (\<beta>, t) # snd \<sigma>') \<in> seq ars\<close> fst_conv ih seq_tail1(3) snd_conv surjective_pairing)
   moreover have "set_mset (measure r (?\<sigma>,\<tau>)) \<subseteq> dm r M" using diff ih dic unfolding measure_def labels_def dm_def by auto
   ultimately show ?thesis by blast
  next
   case False hence step:"(t,\<beta>,s) \<in> ars" using conv_tail1(3) Cons(2) unfolding dec by auto
   hence "(t,[(\<beta>,s)]) \<in> seq ars" using seq.intros by metis
   hence p:"peak ars ((t,[(\<beta>,s)]),\<sigma>')" (is "peak ars ?y") using seq.intros unfolding peak_def using ih by auto
   hence mp: "set_mset (measure r ?y) \<subseteq> ds r (set_mset M)" using ih dic unfolding measure_def labels_def dm_def
     by simp
   hence ne: "M \<noteq> {#}" using dec dic unfolding dm_def ds_def by auto
   hence x:"(measure r ?y,M) \<in> mul r" using mp unfolding dm_def mul_def apply auto by (metis add_0)
   have "({#fst \<alpha>_step#}+{#fst \<beta>_step#},measure r ?P) \<in> mul_eq r" unfolding assms(2) measure_def labels_def apply auto
    unfolding union_lcomm union_assoc[symmetric]  using mul_eq_add_right[where M="{#fst \<alpha>_step#}+{#fst \<beta>_step#}"] unfolding union_assoc by auto
   hence  "(M,measure r ?P) \<in> mul_eq r" using assms(5) mul_eq_trans t by (auto simp: add_mset_commute)
   hence w:"(?y,?P) \<in> pex r" unfolding assms(1) pex_def using mul_and_mul_eq_imp_mul[OF t x] by auto
   obtain \<sigma>'' \<tau>'' where DD:"DD ars r ((t,[(\<beta>,s)]),\<sigma>',\<sigma>'',\<tau>'')" using IH[OF w p] by auto
   have sigma: "\<sigma>'' \<in> seq ars" "fst \<sigma>'' = fst (s, t' # ts)" "lst \<sigma>'' = lst \<tau>''" using DD unfolding DD_def diagram_def lst_def by auto
   have tau'': "\<tau>'' \<in> seq ars" and eq: "lst \<tau> = fst \<tau>''" using DD  unfolding DD_def diagram_def using ih by auto
   have tau:"(fst \<tau>,snd \<tau> @ snd \<tau>'') \<in> seq ars" (is "?\<tau>''' \<in> _") and "lst \<tau>'' = lst (fst \<tau>,snd \<tau>@ snd \<tau>'')" using seq_concat[OF _ tau'' eq] ih by auto
   hence tau2: "fst ?\<tau>''' = lst_conv (s,t'#ts)" "lst \<sigma>'' = lst ?\<tau>'''" using DD ih unfolding DD_def diagram_def dec lst_conv.simps by auto
   have "set_mset (measure r (\<sigma>'',\<tau>'')) \<subseteq> ds r (set_mset M)" using DD_subset_ds[OF t DD mp] unfolding measure_def by auto
   hence "set_mset (r|labels \<sigma>''| + r|labels \<tau>| + (r|labels \<tau>''| -s (dl r (labels \<tau>)) )) \<subseteq> dm r M" using ih unfolding measure_def dm_def diff_def by auto
   hence fin: "set_mset (measure r (\<sigma>'',?\<tau>''')) \<subseteq> dm r M"  unfolding measure_def labels_def apply auto unfolding lemma3_2_2 by auto
   show ?thesis using sigma tau tau2 fin by blast
  qed
 qed
qed

lemma labels_multiset: assumes "length (labels \<sigma>) \<le> 1" and "set (labels \<sigma>) \<subseteq> {\<alpha>}" shows "(r|labels \<sigma>|, {#\<alpha>#}) \<in> mul_eq r"  proof (cases "snd \<sigma>")
 case Nil hence "r|labels \<sigma>| = {#}" unfolding labels_def by auto
 thus ?thesis unfolding mul_eq_def by auto
next
 case (Cons x xs) hence l:"length (labels \<sigma>) = 1" using assms(1) unfolding labels_def by auto
 from this have "labels \<sigma> \<noteq> []" by auto
 from this obtain a as where "labels \<sigma> = a#as" using neq_Nil_conv by metis
 hence leq: "labels \<sigma> = [a]" using l by auto
 hence "set (labels \<sigma>) = {\<alpha>}" using assms(2) by auto
 hence "(r|labels \<sigma>| ) = {#\<alpha>#}" unfolding leq lexmax.simps diff_def by auto
 thus ?thesis using mul_eq_reflexive by auto
qed

lemma decreasing_imp_local_decreasing:
assumes t:"trans r" and i:"irrefl r" and DD: "DD ars r (\<tau>,\<sigma>,\<sigma>',\<tau>')" and "set (labels \<tau>) \<subseteq> ds r {\<beta>}"
and "length (labels \<sigma>) \<le> 1" and "set (labels \<sigma>) \<subseteq> {\<alpha>}"
shows "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. (\<sigma>'=(fst \<sigma>1,snd \<sigma>1@snd \<sigma>2@snd \<sigma>3) \<and> lst \<sigma>1=fst \<sigma>2 \<and> lst \<sigma>2 = fst \<sigma>3 \<and> lst \<sigma>3 = lst \<sigma>'
                 \<and> LD_1' r \<beta> \<alpha> (labels \<sigma>1) (labels \<sigma>2) (labels \<sigma>3))"
      "set (labels \<tau>') \<subseteq> ds r ({\<alpha>,\<beta>})"
proof -
 show "\<exists> \<sigma>1 \<sigma>2 \<sigma>3. (\<sigma>' = (fst \<sigma>1,snd \<sigma>1@snd \<sigma>2@snd \<sigma>3) \<and>
         lst \<sigma>1 = fst \<sigma>2 \<and> lst \<sigma>2 = fst \<sigma>3 \<and> lst \<sigma>3 = lst \<sigma>' \<and> LD_1' r \<beta> \<alpha> (labels \<sigma>1) (labels \<sigma>2) (labels \<sigma>3))" proof -
 from DD have \<sigma>':"\<sigma>' \<in> seq ars" using assms unfolding DD_def diagram_def by auto
 from DD have x: "(r|labels \<sigma>'| -s dl r (labels \<tau>),r|labels \<sigma>| ) \<in> mul_eq r" unfolding DD_def D2_def using D_eq(2)[OF t i] by auto
  have "dl r (labels \<tau>) \<subseteq> ds r (ds r {\<beta>})" using assms(4) unfolding dl_def ds_def by auto
  hence "dl r (labels \<tau>) \<subseteq> ds r {\<beta>}" using ds_ds_subseteq_ds[OF t] by auto
  hence x:"(r|labels \<sigma>'| -s ds r {\<beta>},r|labels \<sigma>| ) \<in> mul_eq r" using x unfolding diff_def by (metis diff_def lemma2_6_8 mul_eq_trans t)
  hence x:"(r|labels \<sigma>'| -s dl r [\<beta>],{#\<alpha>#}) \<in> mul_eq r" using labels_multiset[OF assms(5,6)] unfolding dl_def using mul_eq_trans[OF t x] by auto
  obtain \<sigma>1' \<sigma>2' \<sigma>3' where l:"labels \<sigma>' = \<sigma>1'@(\<sigma>2'@\<sigma>3')" and \<sigma>1'l: "set \<sigma>1' \<subseteq> ds r {\<beta>}" and
   \<sigma>2'l: "length \<sigma>2' \<le> 1 \<and> set \<sigma>2' \<subseteq> {\<alpha>}" and \<sigma>3'l: "set \<sigma>3' \<subseteq> ds r {\<alpha>,\<beta>}" using proposition3_4_inv_lists[OF t i x] unfolding dl_def by auto
  obtain \<sigma>1 \<sigma>23 where \<sigma>1:"\<sigma>1 \<in> seq ars" and \<sigma>23: "\<sigma>23 \<in> seq ars" and lf1: "lst \<sigma>1 = fst \<sigma>23" and lf1b: "lst \<sigma>' = lst \<sigma>23" and
   \<sigma>'_eq:"\<sigma>' = (fst \<sigma>1,snd \<sigma>1@snd \<sigma>23)" and \<sigma>1l:"labels \<sigma>1 = \<sigma>1'" and l2:"labels \<sigma>23 = \<sigma>2'@\<sigma>3'"
   using seq_decompose[OF \<sigma>' l] by auto
  obtain \<sigma>2 \<sigma>3 where \<sigma>2:"\<sigma>2 \<in> seq ars" and \<sigma>3:"\<sigma>3 \<in> seq ars" and lf2:"lst \<sigma>2 = fst \<sigma>3" and lf2b:"lst \<sigma>23 = lst \<sigma>3" and
   \<sigma>23_eq:"\<sigma>23 = (fst \<sigma>2,snd \<sigma>2@snd \<sigma>3)" and \<sigma>2l: "labels \<sigma>2 = \<sigma>2'" and \<sigma>3l: "labels \<sigma>3 = \<sigma>3'"
   using seq_decompose[OF \<sigma>23 l2] by auto
  have "\<sigma>' = (fst \<sigma>1, snd \<sigma>1 @ snd \<sigma>2 @ snd \<sigma>3)" using \<sigma>1 \<sigma>2 \<sigma>3 \<sigma>'_eq \<sigma>23_eq by auto
  moreover have "lst \<sigma>1 = fst \<sigma>2" using lf1 \<sigma>23_eq by auto
  moreover have "lst \<sigma>2 = fst \<sigma>3" using lf2 by auto
  moreover have "lst \<sigma>3 = lst \<sigma>'" using lf1b lf2b by auto
  moreover have "set (labels \<sigma>1) \<subseteq> ds r {\<beta>}" using \<sigma>1l \<sigma>1'l by auto
  moreover have "length (labels \<sigma>2) \<le> 1 \<and> set (labels \<sigma>2) \<subseteq> {\<alpha>}" using \<sigma>2l \<sigma>2'l by auto
  moreover have "set (labels \<sigma>3) \<subseteq> ds r {\<alpha>, \<beta>}" using \<sigma>3l \<sigma>3'l by auto
  ultimately show ?thesis unfolding LD_1'_def by fast
 qed
 show "set (labels \<tau>') \<subseteq> ds r ({\<alpha>,\<beta>})" proof -
  have x:"(r|labels \<tau>'| -s dl r (labels \<sigma>),r|labels \<tau>| ) \<in> mul_eq r" using DD D_eq[OF t i] unfolding DD_def D2_def by auto
  have y:"set_mset r|labels \<tau>| \<subseteq> ds r {\<beta>}" using leq_imp_subseteq[OF lexmax_le_multiset[OF t]] assms(4) by auto
  hence  "set_mset (r|labels \<tau>'|-s ds r (set (labels \<sigma>))) \<subseteq> ds r {\<beta>}" using mul_eq_and_ds_imp_ds[OF t x y] unfolding dl_def by auto
  hence "set_mset (r|labels \<tau>'| ) \<subseteq> ds r {\<beta>} \<union> ds r (set (labels \<sigma>))" unfolding diff_def by auto
  hence "set_mset (r|labels \<tau>'| ) \<subseteq> ds r {\<alpha>,\<beta>}" using assms(6) unfolding ds_def by auto
  thus ?thesis using lexmax_set[OF t] by auto
 qed
qed

lemma local_decreasing_extended_imp_decreasing:
assumes "LT1 ars r (s,[\<beta>_step]) (s,[\<alpha>_step]) \<gamma>1 \<gamma>2 \<gamma>3"
and t: "trans r" and i: "irrefl r"
and IH:"!!y . ((y,((s,[\<beta>_step]@\<upsilon>_step),(s,[\<alpha>_step]@\<rho>_step))) \<in> pex r \<Longrightarrow> peak ars y \<Longrightarrow> \<exists>\<sigma>' \<tau>'. DD ars r (fst y, snd y, \<sigma>', \<tau>'))" (is "!!y. ((y,?P) \<in> _ \<Longrightarrow> _ \<Longrightarrow> _)")
shows "\<exists> \<sigma>1 \<sigma>2 \<sigma>3' \<gamma>1'''. ({\<sigma>1,\<sigma>2,\<sigma>3',\<gamma>1'''} \<subseteq> seq ars \<and>
  set (labels \<sigma>1) \<subseteq> ds r {fst \<beta>_step} \<and> length (labels \<sigma>2) \<le> 1 \<and> set (labels \<sigma>2) \<subseteq> {fst \<alpha>_step} \<and> set (labels \<sigma>3') \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}) \<and>
  set (labels \<gamma>1''') \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step} \<and>
  snd \<beta>_step = fst \<sigma>1 \<and> lst \<sigma>1 = fst \<sigma>2 \<and> lst \<sigma>2 = fst \<sigma>3' \<and> lst \<sigma>3' = lst \<gamma>1''' \<and> fst \<gamma>1''' = fst \<gamma>3"
proof -
 from assms labels_multiset have s2:"(r|labels \<gamma>2|,{#fst \<alpha>_step#}) \<in> mul_eq r" unfolding LT1_def local_triangle1_def LD_1'_def labels_def by auto
 from assms have \<gamma>1: "\<gamma>1 \<in> conv ars" and \<gamma>3: "\<gamma>3 \<in> conv ars" and \<gamma>2_l: "length (labels \<gamma>2) \<le> 1"
  and \<gamma>2_s: "set (labels \<gamma>2) \<subseteq> {fst \<alpha>_step}" and \<gamma>3_s: "set (labels_conv \<gamma>3) \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}"
  and "set (labels_conv \<gamma>1) \<subseteq> ds r {fst \<beta>_step}" unfolding LT_def LD'_def LT1_def LD_1'_def labels_def local_triangle1_def by auto
 hence "set_mset (measure_conv r \<gamma>1) \<subseteq> ds r {fst \<beta>_step}" unfolding measure_conv_def using lexmax_le_multiset[OF t] by (metis set_mset_mset submultiset_implies_subset subset_trans)
 hence \<gamma>1_s: "set_mset (measure_conv r \<gamma>1) \<subseteq> dm r {#fst \<beta>_step#}" unfolding dm_def by auto
 have x: "({#fst \<beta>_step#}, {#fst \<beta>_step, fst \<alpha>_step#}) \<in> mul_eq r" using mul_eq_add_right[of "{#_#}"] by auto
 obtain \<gamma>1' \<gamma>1'' where \<gamma>1': "\<gamma>1' \<in> seq ars" and \<gamma>1'': "\<gamma>1'' \<in> seq ars" and eqx:"fst \<gamma>1' = fst \<gamma>1"
  and  "fst \<gamma>1'' = lst_conv \<gamma>1" and \<gamma>1'_eq: "lst \<gamma>1' = lst \<gamma>1''"  and m2: "set_mset (measure r (\<gamma>1',\<gamma>1'')) \<subseteq> dm r {#fst \<beta>_step#}"
  using conv_imp_valley[OF t IH \<gamma>1 \<gamma>1_s x] apply auto by fast
 hence Q:"peak ars (\<gamma>1'',\<gamma>2)" (is "peak ars ?Q") unfolding peak_def using assms(1) unfolding LT_def LD'_def LT1_def local_triangle1_def by auto
 from m2 have  \<gamma>1's: "set (labels \<gamma>1') \<subseteq> ds r {fst \<beta>_step}" and \<gamma>1''s: "set (labels \<gamma>1'') \<subseteq> ds r {fst \<beta>_step}" unfolding measure_def dm_def using lexmax_set[OF t] by auto
 from m2 have \<tau>1'_m:"(r|labels \<gamma>1''|,{#fst \<beta>_step#}) \<in> mul r" unfolding measure_def mul_def apply auto by (metis dm_def empty_neutral(1) set_mset_single add_mset_not_empty)
 hence y:"(r|labels \<gamma>1''| + r|labels \<gamma>2|,{#fst \<alpha>_step#}+{#fst \<beta>_step#}) \<in> mul r" using mul_add_mul_eq_imp_mul[OF \<tau>1'_m s2] union_commute by metis
 have "(r|labels \<gamma>1''| + r|labels \<gamma>2|, {#fst \<alpha>_step,fst \<beta>_step#} + (r|map fst \<rho>_step|-sds r {fst \<alpha>_step} + r|map fst \<upsilon>_step|-sds r {fst \<beta>_step})) \<in> mul r" using mul_add_right[OF y] by (auto simp: add_mset_commute)
 hence q:"(?Q,?P) \<in> pex r"  unfolding pex_def measure_def labels_def apply auto by (metis union_assoc union_commute union_lcomm)
 obtain \<gamma>1''' \<sigma>' where DD:"DD ars r (\<gamma>1'',\<gamma>2,\<sigma>',\<gamma>1''')" using IH[OF q Q] by auto
 from DD have \<sigma>': "\<sigma>' \<in> seq ars" and \<gamma>1''':"\<gamma>1''' \<in> seq ars" unfolding DD_def diagram_def by auto
 from decreasing_imp_local_decreasing[OF t i DD \<gamma>1''s \<gamma>2_l \<gamma>2_s] obtain \<sigma>1' \<sigma>2' \<sigma>3' where \<sigma>'_dec: "\<sigma>' = (fst \<sigma>1', snd \<sigma>1' @ snd \<sigma>2' @ snd \<sigma>3')"
   and eq1: "lst \<sigma>1' = fst \<sigma>2'" "lst \<sigma>2' = fst \<sigma>3'" "lst \<sigma>3' = lst \<sigma>'"
   and \<sigma>1s: "set (labels \<sigma>1') \<subseteq> ds r {fst \<beta>_step}" and \<sigma>2l: "length (labels \<sigma>2') \<le> 1" and \<sigma>2's: "set (labels \<sigma>2') \<subseteq> {fst \<alpha>_step}" and "set (labels \<sigma>3') \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}"
   and \<sigma>3's: "set (labels \<sigma>3') \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}" and \<gamma>1'''s: "set (labels \<gamma>1''') \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}" unfolding LD_1'_def by blast
 have \<sigma>'_ds: "(fst \<sigma>1', snd \<sigma>1' @ snd \<sigma>2' @ snd \<sigma>3') \<in> seq ars" using \<sigma>' \<sigma>'_dec by auto
 have \<sigma>1':"\<sigma>1' \<in> seq ars" and tmp: "(fst \<sigma>2',snd \<sigma>2'@snd \<sigma>3') \<in> seq ars" using seq_chop[OF \<sigma>'_ds] surjective_pairing eq1 by auto
 have \<sigma>2': "\<sigma>2' \<in> seq ars" and \<sigma>3': "\<sigma>3' \<in> seq ars" using seq_chop[OF tmp] using surjective_pairing eq1 by auto
 have eq:"lst \<gamma>1' = fst \<sigma>1'" using DD \<gamma>1'_eq unfolding DD_def diagram_def apply auto unfolding \<sigma>'_dec by auto
 have \<sigma>1: "(fst \<gamma>1',snd \<gamma>1'@snd \<sigma>1') \<in> seq ars" (is "?\<sigma>1 \<in> _") and eq0:"lst (fst \<gamma>1', snd \<gamma>1' @ snd \<sigma>1') = lst \<sigma>1'" using seq_concat[OF \<gamma>1' \<sigma>1' eq] by auto
 moreover have "set (labels ?\<sigma>1) \<subseteq> ds r {fst \<beta>_step}" using \<sigma>1s \<gamma>1's unfolding labels_def dm_def by auto
 moreover have "snd \<beta>_step = fst ?\<sigma>1" using assms(1) unfolding LT1_def local_triangle1_def lst_def \<sigma>'_dec eqx by auto
 moreover have "lst ?\<sigma>1 = fst \<sigma>2'" unfolding eq0 eq1 by auto
 moreover have "lst \<sigma>3' = lst \<gamma>1'''" unfolding eq1 using DD unfolding DD_def diagram_def by auto
 moreover have "fst \<gamma>1''' = fst \<gamma>3" using DD assms(1) unfolding DD_def diagram_def LT1_def local_triangle1_def by auto
 ultimately show ?thesis using \<sigma>2' \<sigma>2's \<sigma>3' \<sigma>3's  \<gamma>1''' \<gamma>1'''s eq1 surjective_pairing \<sigma>2l by blast
qed

lemma LDD_imp_DD:
assumes t:"trans r" and i:"irrefl r" and "LDD ars r (\<tau>,\<sigma>,\<sigma>1,\<sigma>2,\<sigma>3,\<tau>1,\<tau>2,\<tau>3)"
shows "\<exists> \<sigma>' \<tau>'. DD ars r (\<tau>,\<sigma>,\<sigma>',\<tau>')" proof -
 from assms have "length (labels \<sigma>) = 1"  unfolding LDD_def LDD1_def local_diagram1_def local_peak_def unfolding labels_def by auto
 from this obtain \<alpha> where l: "labels \<sigma> = [\<alpha>]" by (metis append_Nil append_butlast_last_id butlast_conv_take diff_self_eq_0 length_0_conv take_0 zero_neq_one)
 hence \<sigma>l: "labels \<sigma> = [hd (labels \<sigma>)]" by auto
 from assms have "length (labels \<tau>) = 1"  unfolding LDD_def LDD1_def local_diagram1_def local_peak_def unfolding labels_def by auto
 from this obtain \<beta> where l: "labels \<tau> = [\<beta>]" by (metis append_Nil append_butlast_last_id butlast_conv_take diff_self_eq_0 length_0_conv take_0 zero_neq_one)
 hence \<tau>l: "labels \<tau> = [hd (labels \<tau>)]" by auto
 from assms have \<sigma>':"(fst \<sigma>1,snd \<sigma>1@snd \<sigma>2@snd \<sigma>3) \<in> seq ars" (is "?\<sigma>' \<in> _") and \<tau>':"(fst \<tau>1,snd \<tau>1@snd \<tau>2@snd \<tau>3) \<in> seq ars" (is "?\<tau>' \<in> _")
  unfolding LDD_def LDD1_def local_diagram1_def local_peak_def peak_def apply auto apply (metis fst_eqD seq_concat(1) snd_eqD)  by (metis fst_eqD seq_concat(1) snd_eqD)
 from assms have sigmas: "fst ?\<sigma>' = fst \<sigma>1" "lst ?\<sigma>' = lst \<sigma>3" unfolding LDD_def LDD1_def local_diagram1_def local_peak_def peak_def apply auto by (metis (hide_lams, no_types) \<sigma>' append_assoc seq_chop(1) seq_concat(2) seq_concat_helper)
 from assms have taus: "fst ?\<tau>' = fst \<tau>1" "lst ?\<tau>' = lst \<tau>3" unfolding LDD_def LDD1_def local_diagram1_def local_peak_def peak_def apply auto  by (metis (hide_lams, no_types) \<tau>' append_assoc seq_chop(1) seq_concat(2) seq_concat_helper)
 have "diagram ars (\<tau>,\<sigma>,?\<sigma>',?\<tau>')" using assms unfolding LDD_def LDD1_def local_diagram1_def diagram_def local_peak_def apply auto
  unfolding peak_def apply auto using sigmas taus \<sigma>' \<tau>' by auto
 moreover have "D2 r (\<tau>,\<sigma>,?\<sigma>',?\<tau>')" using assms proposition3_4[OF t i] \<sigma>l \<tau>l unfolding LDD_def LDD1_def D2_def LD'_def labels_def by auto
 ultimately show ?thesis unfolding DD_def by auto
qed

lemma LT_imp_DD:
assumes t:"trans r"
and i:"irrefl r"
and IH:"!!y . ((y,((s,[\<beta>_step]@\<upsilon>_step),(s,[\<alpha>_step]@\<rho>_step))) \<in> pex r \<Longrightarrow> peak ars y \<Longrightarrow> \<exists>\<sigma>' \<tau>'. DD ars r (fst y, snd y, \<sigma>', \<tau>'))" (is "!!y. ((y,?P) \<in> _ \<Longrightarrow> _ \<Longrightarrow> _)")
and LT: "LT ars r ((s,[\<beta>_step]),(s,[\<alpha>_step]),\<gamma>1,\<gamma>2,\<gamma>3,\<delta>1,\<delta>2,\<delta>3)"
shows "\<exists> \<kappa> \<mu>. DD ars r ((s,[\<beta>_step]),(s,[\<alpha>_step]),\<kappa>,\<mu>)"
proof -
    from LT have LTa: "LT1 ars r (s,[\<beta>_step]) (s,[\<alpha>_step]) \<gamma>1 \<gamma>2 \<gamma>3" and LTb: "LT1 ars r (s,[\<alpha>_step]) (s,[\<beta>_step]) \<delta>1 \<delta>2 \<delta>3" unfolding LT_def by auto

    from local_decreasing_extended_imp_decreasing[OF LTa t i IH] obtain \<sigma>1 \<sigma>2 \<sigma>3' \<gamma>1''' where sigmas:"{\<sigma>1,\<sigma>2,\<sigma>3',\<gamma>1'''} \<subseteq> seq ars" and
    onetwo1: "set (labels \<sigma>1) \<subseteq> ds r {fst \<beta>_step} \<and> length (labels \<sigma>2) \<le> 1 \<and> set (labels \<sigma>2) \<subseteq> {fst \<alpha>_step} \<and>
    set (labels \<sigma>3') \<subseteq> ds r {fst \<alpha>_step, fst \<beta>_step} \<and> set (labels \<gamma>1''') \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step} \<and>
     snd \<beta>_step = fst \<sigma>1 \<and> lst \<sigma>1 = fst \<sigma>2 \<and> lst \<sigma>2 = fst \<sigma>3' \<and> lst \<sigma>3' = lst \<gamma>1''' \<and> fst \<gamma>1''' = fst \<gamma>3" by metis

    have ih2: "!!y. (y, (s, [\<alpha>_step] @ \<rho>_step),(s,[\<beta>_step] @ \<upsilon>_step)) \<in> pex r \<Longrightarrow> peak ars y \<Longrightarrow> \<exists>\<sigma>' \<tau>'. DD ars r (fst y, snd y, \<sigma>', \<tau>')"
    using IH unfolding pex_def measure_def by (auto simp: union_commute)

    from local_decreasing_extended_imp_decreasing[OF LTb t i ih2] obtain \<tau>1 \<tau>2 \<tau>3' \<delta>1''' where taus:"{\<tau>1,\<tau>2,\<tau>3',\<delta>1'''} \<subseteq> seq ars" and
    onetwo2: "set (labels \<tau>1) \<subseteq> ds r {fst \<alpha>_step} \<and> length (labels \<tau>2) \<le> 1 \<and> set (labels \<tau>2) \<subseteq> {fst \<beta>_step} \<and>
    set (labels \<tau>3') \<subseteq> ds r {fst \<beta>_step,fst \<alpha>_step} \<and> set (labels \<delta>1''') \<subseteq> ds r {fst \<beta>_step,fst \<alpha>_step} \<and>
     snd \<alpha>_step = fst \<tau>1 \<and> lst \<tau>1 = fst \<tau>2 \<and> lst \<tau>2 = fst \<tau>3' \<and> lst \<tau>3' = lst \<delta>1''' \<and> fst \<delta>1''' = fst \<delta>3" by metis

    have \<gamma>3: "\<gamma>3 \<in> conv ars" and \<gamma>3m:"set (labels_conv \<gamma>3) \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}" and
         \<delta>3: "\<delta>3 \<in> conv ars" (is "?c2 \<in> _") and \<delta>3m: "set (labels_conv \<delta>3) \<subseteq> ds r {fst \<beta>_step,fst \<alpha>_step}" and
         eq: "lst_conv \<gamma>3 = lst_conv \<delta>3" using LT unfolding LT_def LT1_def local_triangle1_def LD_1'_def labels_def by auto
    hence \<delta>3m: "set (labels_conv \<delta>3) \<subseteq> ds r {fst \<alpha>_step, fst \<beta>_step}" using insert_commute by metis

    (*concat*)
    have \<delta>1''': "\<delta>1''' \<in> seq ars" using taus by auto
    have \<gamma>1''': "\<gamma>1''' \<in> seq ars" using sigmas by auto
    have c1: "(fst \<delta>1''',map (Pair True) (snd \<delta>1''')) \<in> conv ars" (is "?c0 \<in> _")
      using seq_imp_conv \<delta>1''' surjective_pairing by metis
    have c11: "lst \<delta>1''' = lst_conv ?c0" using seq_imp_conv \<delta>1''' surjective_pairing by metis
    have c1l: "set (labels_conv ?c0) \<subseteq> ds r {fst \<beta>_step,fst \<alpha>_step}" using onetwo2 seq_imp_conv \<delta>1''' surjective_pairing by metis
    hence c1l:"set (labels_conv ?c0) \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}" using insert_commute by metis

    have c1: "conv_mirror ?c0 \<in> conv ars" (is "?c1 \<in> _")
             "set (labels_conv (conv_mirror ?c0)) \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}"
             "fst (conv_mirror ?c0) = lst \<tau>3'"
             "lst_conv (conv_mirror ?c0) = fst \<delta>3"
     using conv_mirror[OF c1] c11 c1l c1 onetwo2 by auto


    have c2: "?c2 \<in> conv ars"
             "set (labels_conv ?c2) \<subseteq> ds r {fst \<alpha>_step, fst \<beta>_step}"
             "fst ?c2 = fst \<delta>3"
             "lst_conv ?c2 = lst_conv \<gamma>3" using \<delta>3 eq \<delta>3m by auto

    have "conv_mirror \<gamma>3 \<in> conv ars" (is "?c3 \<in> _") "set (labels_conv (conv_mirror \<gamma>3)) = set (labels_conv \<gamma>3)" using conv_mirror[OF \<gamma>3] by auto
    hence c3: "?c3 \<in> conv ars"
              "set (labels_conv ?c3) \<subseteq> ds r {fst \<alpha>_step, fst \<beta>_step}"
              "fst ?c3 = lst_conv \<delta>3"
              "lst_conv ?c3 = fst \<gamma>1'''" using conv_mirror[OF \<gamma>3] eq onetwo1 \<gamma>3m by auto

    have c4: "(fst \<gamma>1''',map (Pair True) (snd \<gamma>1''')) \<in> conv ars" (is "?c4 \<in> _") "set (labels_conv (fst \<gamma>1''',map (Pair True) (snd \<gamma>1'''))) = set (labels \<gamma>1''')"
     using seq_imp_conv \<gamma>1''' surjective_pairing apply metis using seq_imp_conv \<gamma>1''' surjective_pairing by metis
    have c4: "?c4 \<in> conv ars"
             "lst_conv ?c4 = lst \<gamma>1'''"
             "set (labels_conv ?c4) \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}"
     using  seq_imp_conv \<gamma>1''' surjective_pairing apply metis using seq_imp_conv \<gamma>1''' surjective_pairing apply metis using c4(2) onetwo1 by auto

    have eq: "lst_conv ?c1 = fst ?c2" using c1 c2 by auto
    have c12: "(fst ?c1,snd ?c1@snd ?c2) \<in> conv ars" (is "?c12 \<in> _")
     "fst (fst ?c1,snd ?c1@snd ?c2) = fst ?c1" "lst_conv (fst ?c1,snd ?c1@snd ?c2) = lst_conv ?c2" using conv_concat[OF c1(1) c2(1) eq] by auto
    have eq: "lst_conv ?c12 = fst ?c3" using c12 c3 by auto
    have c123: "(fst ?c12,snd ?c12@snd ?c3) \<in> conv ars" (is "?c123 \<in> _")
     "fst (fst ?c12,snd ?c12@snd ?c3) = fst ?c12" "lst_conv (fst ?c12,snd ?c12@snd ?c3) = lst_conv ?c3" using conv_concat[OF c12(1) c3(1) eq] by auto

    have eq: "lst_conv ?c123 = fst ?c4" using c123 c2 c4 onetwo1 onetwo2 apply auto unfolding Let_def using c3(4) apply auto by metis
    have c1234: "(fst ?c123,snd ?c123@snd ?c4) \<in> conv ars" (is "?c1234 \<in> _")
     "fst (fst ?c123,snd ?c123@snd ?c4) = fst ?c123" "lst_conv (fst ?c123,snd ?c123@snd ?c4) = lst_conv ?c4" using conv_concat[OF c123(1) c4(1) eq] by auto
    hence c1234: "?c1234 \<in> conv ars" (is "?c1234 \<in> _")
     "fst (?c1234) = lst \<tau>3'" "lst_conv ?c1234 = lst \<sigma>3'" apply auto unfolding Let_def using c1(3) apply auto apply metis using c4(2) onetwo1 by metis

    have c12l: "set (labels_conv ?c12) \<subseteq> ds r {fst \<alpha>_step, fst \<beta>_step}" using conv_concat_labels[OF c1(1) c2(1)] c1 c2 by auto
    have c123l: "set (labels_conv ?c123) \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}" using conv_concat_labels[OF c12(1) c3(1)] c12l c3 by auto
    have c1234l:"set (labels_conv ?c1234) \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}" using conv_concat_labels[OF c123(1) c4(1)] c123l c4 by auto
    hence "set_mset (r|labels_conv ?c1234| ) \<subseteq> ds r {fst \<alpha>_step,fst \<beta>_step}" using submultiset_implies_subset[OF lexmax_le_multiset[OF t]] by auto
    hence "set_mset (measure_conv r ?c1234) \<subseteq> dm r {#fst \<beta>_step, fst \<alpha>_step#}" unfolding measure_conv_def dm_def by (auto simp: add_mset_commute)
    hence m: "set_mset (measure_conv r ?c1234) \<subseteq> dm r {#fst \<alpha>_step, fst \<beta>_step#}" by (auto simp: add_mset_commute)

    from c1234 m obtain \<rho> where \<rho>:"\<rho> \<in> conv ars" and \<rho>m:"set_mset (measure_conv r \<rho>) \<subseteq> dm r {# fst \<alpha>_step, fst \<beta>_step#}"
    and eq1: "fst \<rho> = lst \<tau>3'" and eq2: "lst_conv \<rho> = lst \<sigma>3'" by auto

    have M:"({#fst \<alpha>_step,fst \<beta>_step#},{#fst \<beta>_step,fst \<alpha>_step#}) \<in> mul_eq r" using mul_eq_reflexive add_mset_commute by metis
    from conv_imp_valley[OF t IH \<rho> \<rho>m M] obtain \<tau>3'' \<sigma>3'' where
     \<tau>3'':"\<tau>3'' \<in> seq ars" and \<sigma>3'': "\<sigma>3'' \<in> seq ars" and eq:"fst \<tau>3'' = fst \<rho> \<and> fst \<sigma>3'' = lst_conv \<rho> \<and> lst \<tau>3'' = lst \<sigma>3'' \<and>
    set_mset (measure r (\<tau>3'', \<sigma>3'')) \<subseteq> dm r {#fst \<alpha>_step, fst \<beta>_step#}"  apply auto by fast
    have s1: "set (labels \<sigma>3'') \<subseteq> ds r {fst \<alpha>_step, fst \<beta>_step}" using eq unfolding dm_def measure_def apply auto by (metis (hide_lams, no_types) insert_commute lexmax_set subsetD t)
    have s2: "set (labels \<tau>3'') \<subseteq> ds r {fst \<beta>_step, fst \<alpha>_step}" using eq unfolding dm_def measure_def apply auto by (metis (hide_lams, no_types) insert_commute lexmax_set subsetD t)
    have \<sigma>1_eq: "lst (s, [\<beta>_step]) = fst \<sigma>1" and \<tau>1_eq: "lst (s, [\<alpha>_step]) = fst \<tau>1" using onetwo1 onetwo2 surjective_pairing unfolding lst_def by auto
    have eqn: " lst \<tau>3'' = lst \<sigma>3''" and \<sigma>_eq: "lst \<sigma>3' = fst \<sigma>3''" and \<tau>_eq: "lst \<tau>3' = fst \<tau>3''" using eq eq1 eq2 by auto
    have \<sigma>3':"(fst \<sigma>3',snd \<sigma>3'@snd \<sigma>3'') \<in> seq ars" (is "?\<sigma>3 \<in> _") using seq_concat[OF _ \<sigma>3'' \<sigma>_eq] sigmas by blast
    have \<tau>3':"(fst \<tau>3',snd \<tau>3'@snd \<tau>3'') \<in> seq ars" (is "?\<tau>3 \<in> _") using seq_concat[OF _ \<tau>3'' \<tau>_eq] taus by blast
    have "fst ?\<sigma>3 = lst \<sigma>2" and "fst ?\<tau>3 = lst \<tau>2" using onetwo1 onetwo2 by auto
    have lst:"lst ?\<sigma>3 = lst ?\<tau>3" using eqn \<sigma>3'' \<sigma>3' \<sigma>_eq \<tau>3'' \<tau>_eq \<tau>3' seq_chop(1) seq_concat(2) surjective_pairing by metis
    have "local_diagram1 ars (s, [\<beta>_step]) (s, [\<alpha>_step]) \<sigma>1 \<sigma>2 (fst \<sigma>3', snd \<sigma>3' @ snd \<sigma>3'')"
     using sigmas \<sigma>3' onetwo1 \<sigma>1_eq LT unfolding local_diagram1_def  LT_def LT1_def local_triangle1_def by auto
    moreover have "local_diagram1 ars (s,[\<alpha>_step]) (s,[\<beta>_step]) \<tau>1 \<tau>2 (fst \<tau>3',snd \<tau>3'@snd \<tau>3'')"
     using taus \<tau>3' onetwo2 \<tau>1_eq LT unfolding local_diagram1_def LT_def LT1_def local_triangle1_def by auto
    moreover have "LD_1' r (hd (labels (s, [\<beta>_step]))) (hd (labels (s, [\<alpha>_step]))) (labels \<sigma>1) (labels \<sigma>2) (labels (fst \<sigma>3', snd \<sigma>3' @ snd \<sigma>3''))"
     using onetwo1 s1 unfolding LD_1'_def labels_def by auto
    moreover have "LD_1' r (hd (labels (s, [\<alpha>_step]))) (hd (labels (s, [\<beta>_step]))) (labels \<tau>1) (labels \<tau>2) (labels (fst \<tau>3', snd \<tau>3' @ snd \<tau>3''))"
     using onetwo2 s2 unfolding LD_1'_def labels_def by auto
    ultimately have LDD: "LDD ars r ((s,[\<beta>_step]),(s,[\<alpha>_step]),\<sigma>1,\<sigma>2,?\<sigma>3,\<tau>1,\<tau>2,?\<tau>3)" using lst unfolding LDD_def LDD1_def local_diagram1_def by auto
    from LDD_imp_DD[OF t i LDD] show ?thesis by auto
qed

lemma LT_imp_D: assumes t:"trans r" and "wf r" and "\<forall>p. (local_peak ars p \<longrightarrow> (\<exists> \<gamma>1 \<gamma>2 \<gamma>3 \<delta>1 \<delta>2 \<delta>3. LT ars r (fst p,snd p,\<gamma>1,\<gamma>2,\<gamma>3,\<delta>1,\<delta>2,\<delta>3)))"
and "peak ars P" shows "(\<exists> \<sigma>' \<tau>'. DD ars r (fst P,snd P,\<sigma>',\<tau>'))" proof -
 have i: "irrefl r" using assms(1,2) acyclic_irrefl trancl_id wf_acyclic by metis
 have wf: "wf (pex r)" using wf[OF assms(1,2)] .
 show ?thesis using assms(4) proof (induct rule:wf_induct_rule[OF wf])
  case (1 P)
  obtain s \<tau> \<sigma> where decompose:"P = (\<tau>,\<sigma>)" and tau:"\<tau> \<in> seq ars" and sigma:"\<sigma> \<in> seq ars"
   and tau_s: "fst \<tau> = s" and sigma_s: "fst \<sigma> = s" using 1 unfolding peak_def by auto
  show ?case proof (cases "snd \<tau>")
   case Nil from mirror_DD[OF assms(1) i trivial_DD[OF sigma]]
   show ?thesis using tau_s sigma_s Nil surjective_pairing unfolding decompose fst_conv snd_conv DD_def by metis
  next
   case (Cons \<beta>_step \<upsilon>_step)
   hence tau_dec: "\<tau> = (s,[\<beta>_step]@\<upsilon>_step)" apply auto using tau_s surjective_pairing by metis
   hence tau2:" (s,[\<beta>_step]@\<upsilon>_step) \<in> seq ars" using tau by auto
   show ?thesis proof (cases "snd \<sigma>")
    case Nil from trivial_DD[OF tau]
    show ?thesis using tau_s sigma_s Nil surjective_pairing unfolding decompose fst_conv snd_conv DD_def by metis
   next
    case (Cons \<alpha>_step \<rho>_step)
    hence sigma_dec: "\<sigma> = (s,[\<alpha>_step]@\<rho>_step)" apply auto using sigma_s surjective_pairing by metis
    hence sigma2:"(s,[\<alpha>_step]@\<rho>_step) \<in> seq ars" using sigma by auto

    have alpha:"(s,[\<alpha>_step]) \<in> seq ars" (is "?\<alpha> \<in> _")
     and rho: "(lst (s,[\<alpha>_step]),\<rho>_step) \<in> seq ars" (is "?\<rho> \<in> _") using seq_chop[OF sigma2] by auto
    hence alpha': "(s,fst \<alpha>_step, snd \<alpha>_step) \<in> ars" by (metis seq_tail1(2))
    have beta:"(s,[\<beta>_step]) \<in> seq ars" (is "?\<beta> \<in> _")
     and upsilon: "(lst (s,[\<beta>_step]),\<upsilon>_step) \<in> seq ars" (is "?\<upsilon> \<in> _") using seq_chop[OF tau2] by auto

    have lp:"local_peak ars (?\<beta>,?\<alpha>)" using alpha beta unfolding local_peak_def peak_def by auto

   (* difference begin*)
    from this obtain \<gamma>1 \<gamma>2 \<gamma>3 \<delta>1 \<delta>2 \<delta>3 where LT: "LT ars r (?\<beta>, ?\<alpha>, \<gamma>1, \<gamma>2, \<gamma>3, \<delta>1, \<delta>2, \<delta>3)" using assms(3) apply auto by metis
    have P:"P = ((s,[\<beta>_step]@\<upsilon>_step),(s,[\<alpha>_step]@\<rho>_step))" (is "P = ?P") using decompose unfolding tau_dec sigma_dec by auto
    obtain \<kappa> \<mu> where D:"DD ars r (?\<beta>,?\<alpha>,\<kappa>,\<mu>)" using LT_imp_DD[OF t i 1(1) LT] unfolding P by fast
   (*difference end*)

    hence kappa: "\<kappa>\<in>seq ars" and mu: "\<mu>\<in>seq ars" unfolding DD_def diagram_def by auto
    have P_IH1: " peak ars (?\<upsilon>,\<kappa>)" using upsilon kappa D unfolding DD_def diagram_def peak_def by auto
    have beta_ne: "labels ?\<beta> \<noteq> []" unfolding labels_def by auto
    have dec: "D r (labels ?\<beta>) (labels ?\<alpha>) (labels \<kappa>) (labels \<mu>)" using D unfolding DD_def D2_def by auto
    have x1:"((?\<upsilon>,\<kappa>), (\<tau>,?\<alpha>)) \<in> pex r" using lemma3_6[OF assms(1) beta_ne dec]
     unfolding pex_def measure_def decompose labels_def tau_dec apply (auto simp: add_mset_commute) using union_commute by metis
    have "(lexmax r (labels \<tau>) + lexmax r (labels (?\<alpha>)), lexmax r (labels \<tau>) + lexmax r (labels \<sigma>)) \<in> mul_eq r" (is "(?l,?r) \<in> _")
      unfolding sigma_dec labels_def snd_conv list.map lexmax.simps diff_from_empty by (simp add: lemma2_6_2_a t)
    hence "((?\<upsilon>,\<kappa>),P) \<in> pex r" using x1 unfolding sigma_s pex_def measure_def decompose using mul_and_mul_eq_imp_mul[OF assms(1)] by auto
    from this obtain \<kappa>' \<upsilon>' where IH1: "DD ars r (?\<upsilon>,\<kappa>,\<kappa>',\<upsilon>')" using 1(1)[OF _ P_IH1] unfolding decompose by auto
    hence kappa':"\<kappa>'\<in>seq ars" and upsilon': "\<upsilon>'\<in>seq ars" using D unfolding DD_def diagram_def by auto
    have tau': "(fst \<mu>,snd \<mu>@(snd \<upsilon>')) \<in> seq ars" (is "?\<tau>' \<in> _") using seq_concat(1)[OF mu upsilon'] D IH1 unfolding DD_def diagram_def by auto
    have DIH1: "DD ars r (\<tau>,?\<alpha>,\<kappa>',?\<tau>')" using lemma3_5_DD[OF assms(1) i D IH1] tau_dec by auto
    hence dec_dih1: "D r (labels \<tau>) (labels ?\<alpha>) (labels \<kappa>') (labels ?\<tau>')" using DIH1 unfolding DD_def D2_def by simp

    have P_IH2: "peak ars (?\<tau>',?\<rho>)" using tau' rho D unfolding DD_def diagram_def peak_def by auto
    have alpha_ne: "labels ?\<alpha> \<noteq> []" unfolding labels_def by simp
    have "((?\<tau>',?\<rho>),P) \<in> pex r" using lemma3_6_v[OF assms(1) i alpha_ne dec_dih1] unfolding pex_def measure_def decompose labels_def sigma_dec by auto
    from this obtain \<rho>' \<tau>'' where IH2: "DD ars r (?\<tau>',?\<rho>,\<rho>',\<tau>'')" using 1(1)[OF _ P_IH2] by auto
    show ?thesis using lemma3_5_DD_v[OF assms(1) i DIH1 IH2] unfolding decompose fst_conv snd_conv sigma_dec by fast
   qed
  qed
 qed
qed

definition LD_conv :: "'b set \<Rightarrow> 'a rel \<Rightarrow> bool"
 where "LD_conv L ars = (\<exists> (r:: ('b rel)) (lrs::('a,'b) lars). (ars = unlabel lrs) \<and> trans r \<and> wf r \<and> (\<forall>p. (local_peak lrs p \<longrightarrow> (\<exists> \<gamma>1 \<gamma>2 \<gamma>3 \<delta>1 \<delta>2 \<delta>3. LT lrs r (fst p,snd p,\<gamma>1,\<gamma>2,\<gamma>3,\<delta>1,\<delta>2,\<delta>3)))))"

lemma sound_conv: assumes "LD_conv L ars" shows "CR ars"
 using assms LT_imp_D D_imp_CR unfolding LD_conv_def by metis

hide_const (open) D
hide_const (open) seq
hide_const (open) measure

hide_fact (open) split

end
