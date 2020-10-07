 (*
    File:      Group_Adjoin.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Adjoining Elements to a Finite Abelian Group\<close>
theory Group_Adjoin
imports 
  Complex_Main
  "HOL-Algebra.Multiplicative_Group"
begin

text \<open>
  This theory provides the notion of adjoining a single element to a subgroup of a finite
  abelian group, and, in particular, an induction principle based upon this: We can show that
  some property holds for a group by showing that it holds for some fixed subgroup and that
  it is preserved when adjoining a single element.

  The general idea for this was taken from Apostol's 
  ``Analytic Number Theory''~\cite{apostol1976analytic}.
\<close>

subsection \<open>Miscellaneous Group Theory\<close>

lemma (in group) ord_min:
  assumes "m \<ge> 1" "x \<in> carrier G" "x [^] m = \<one>"
  shows   "ord x \<le> m"
  using assms pow_eq_id by auto

lemma (in group) bij_betw_mult_left [intro]:
  assumes [simp]: "x \<in> carrier G"
  shows "bij_betw (\<lambda>y. x \<otimes> y) (carrier G) (carrier G)"
  by (intro bij_betwI[where ?g = "\<lambda>y. inv x \<otimes> y"])
     (auto simp: m_assoc [symmetric])

locale finite_comm_group = comm_group +
  assumes fin [intro]: "finite (carrier G)"
begin

lemma order_gt_0 [simp,intro]: "order G > 0"
  by (subst order_gt_0_iff_finite) auto

lemma subgroup_imp_finite_comm_group:
  assumes "subgroup H G"
  shows   "finite_comm_group (G\<lparr>carrier := H\<rparr>)"
proof -
  interpret G': group "G\<lparr>carrier := H\<rparr>" by (intro subgroup_imp_group) fact+
  interpret H: subgroup H G by fact
  show ?thesis by standard (insert finite_subset[OF H.subset fin], auto simp: m_comm)
qed

end


subsection \<open>Subgroup indicators and adjoining elements\<close>

definition subgroup_indicator :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> nat" where
  "subgroup_indicator G H a = (LEAST k. k > 0 \<and> a [^]\<^bsub>G\<^esub> k \<in> H)"

definition adjoin :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "adjoin G H a = {x \<otimes>\<^bsub>G\<^esub> a [^]\<^bsub>G\<^esub> k |x k. x \<in> H \<and> k < subgroup_indicator G H a}"

lemma (in subgroup) nat_pow_closed [simp,intro]: "a \<in> H \<Longrightarrow> pow G a (n::nat) \<in> H"
  by (induction n) (auto simp: nat_pow_def)

lemma nat_pow_modify_carrier: "a [^]\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> b = a [^]\<^bsub>G\<^esub> (b::nat)"
  by (simp add: nat_pow_def)

lemma subgroup_indicator_modify_carrier [simp]:
  "subgroup_indicator (G\<lparr>carrier := H'\<rparr>) H a = subgroup_indicator G H a"
  by (auto simp: subgroup_indicator_def nat_pow_def)

lemma adjoin_modify_carrier [simp]:
  "adjoin (G\<lparr>carrier := H'\<rparr>) H a = adjoin G H a"
  by (simp_all add: adjoin_def nat_pow_def)

context group
begin

lemma subgroup_indicator_eq_1:
  assumes "a \<in> H" "a \<in> carrier G"
  shows   "subgroup_indicator G H a = 1"
proof -
  from assms show ?thesis
    unfolding subgroup_indicator_def
    by (intro Least_equality) (auto simp: nat_pow_def)
qed

lemma subgroup_indicator_le:
  assumes "a [^] n \<in> H" "n > 0"  "a \<in> carrier G"
  shows   "subgroup_indicator G H a \<le> n"
  using assms unfolding subgroup_indicator_def by (intro Least_le) auto

end

context finite_comm_group
begin

lemma ord_pos: 
  assumes "x \<in> carrier G"
  shows   "ord x > 0"
  using ord_ge_1[of x] assms fin by auto

lemma 
  assumes "subgroup H G" and a: "a \<in> carrier G"
  shows subgroup_indicator_pos: "subgroup_indicator G H a > 0" (is "?h > 0")
  and   pow_subgroup_indicator: "a [^] subgroup_indicator G H a \<in> H"
proof -
  interpret subgroup H G by fact
  from a have "\<exists>h>0. a [^] (h::nat) \<in> H"
    by (intro exI[of _ "ord a"]) (auto simp: ord_pos pow_ord_eq_1 fin)
  hence "?h > 0 \<and> a [^] ?h \<in> H" unfolding subgroup_indicator_def
    by (rule LeastI_ex)
  thus "?h > 0" and "a [^] ?h \<in> H" by auto
qed

lemma subgroup_indicator_le_ord:
  assumes "a \<in> carrier G" "subgroup H G"
  shows   "subgroup_indicator G H a \<le> ord a"
proof -
  interpret subgroup H G by fact
  from assms show ?thesis by (intro subgroup_indicator_le) (auto simp: pow_ord_eq_1 fin ord_pos)
qed

lemma subgroup_indicator_trivial: 
  assumes "a \<in> carrier G"
  shows   "subgroup_indicator G {\<one>} a = group.ord G a"
proof -
  have sg[simp]: "subgroup {\<one>} G" by standard auto
  from pow_subgroup_indicator[OF sg assms] and assms show ?thesis
    by (intro antisym subgroup_indicator_le_ord ord_min)
       (auto simp: Suc_le_eq subgroup_indicator_pos)
qed

lemma mem_adjoin:
  assumes "subgroup H G" "x \<in> H" "a \<in> carrier G"
  shows   "x \<in> adjoin G H a"
proof -
  interpret subgroup H G by fact
  from assms show ?thesis
    by (auto simp: adjoin_def intro!: exI[of _ x] exI[of _ 0] subgroup_indicator_pos)
qed

lemma adjoin_subgroup:
  assumes "subgroup H G" and a: "a \<in> carrier G"
  shows   "subgroup (adjoin G H a) G"
proof (standard, goal_cases)
  case 1
  interpret subgroup H G by fact
  from a show ?case by (auto simp: adjoin_def)
next
  case (2 x y)
  interpret subgroup H G by fact
  define h where "h = subgroup_indicator G H a"
  from assms have [simp]: "h > 0" 
    unfolding h_def by (intro subgroup_indicator_pos) auto
  from 2(1) obtain x' :: 'a and k :: nat where [simp]: "x' \<in> H" "x = x' \<otimes> a [^] k"
    by (auto simp: adjoin_def)
  from 2(2) obtain y' :: 'a and l :: nat where [simp]: "y' \<in> H" "y = y' \<otimes> a [^] l"
    by (auto simp: adjoin_def)
  define a' where "a' = (a [^] h) [^] ((k + l) div h)"
  have [simp]: "a' \<in> H" unfolding a'_def
    by (rule nat_pow_closed) (insert assms, auto simp: h_def intro!: pow_subgroup_indicator)
  from a have "x \<otimes> y = (x' \<otimes> y') \<otimes> a [^] (k + l)"
    by (simp add: nat_pow_mult [symmetric] m_ac)
  also have "k + l = h * ((k + l) div h) + (k + l) mod h"
    by (rule mult_div_mod_eq [symmetric])
  also from a fin have "a [^] \<dots> = a' \<otimes> a [^] ((k + l) mod h)"
    by (subst nat_pow_mult [symmetric]) 
       (simp_all add: nat_pow_pow [symmetric] pow_ord_eq_1 a'_def [symmetric])
  finally have "x \<otimes> y = x' \<otimes> y' \<otimes> a' \<otimes> a [^] ((k + l) mod h)" 
    using a by (simp add: m_ac)
  moreover from a have "(k + l) mod h < h"
    by (intro mod_less_divisor) (auto simp: ord_pos)
  ultimately show ?case
    by (auto simp: adjoin_def h_def intro!: exI[of _ "x' \<otimes> y' \<otimes> a'"] exI[of _ "(k + l) mod h"])
next
  case 3
  interpret subgroup H G by fact
  from assms show ?case
    by (auto simp: adjoin_def intro!: exI[of _ \<one>] exI[of _ 0] subgroup_indicator_pos)
next
  case (4 x)
  interpret H: subgroup H G by fact
  define h where "h = subgroup_indicator G H a"
  define a' where "a' = a [^] h"
  from assms have [simp]: "a' \<in> H" unfolding a'_def h_def
    by (intro pow_subgroup_indicator) auto
  from 4 obtain x' and k :: nat where [simp]: "x' \<in> H" "x = x' \<otimes> a [^] k" and "k < h"
    by (auto simp: adjoin_def h_def)
  show ?case
  proof (cases "k = 0")
    case True
    with assms show ?thesis
      by (auto simp: mem_adjoin)
  next
    case False
    from a have "inv x = inv x' \<otimes> inv (a [^] k)"
      by (simp add: inv_mult)
    also have "\<dots> = inv x' \<otimes> (inv a' \<otimes> a') \<otimes> inv (a [^] k)" by simp
    also have "\<dots> = inv x' \<otimes> inv a' \<otimes> (a' \<otimes> inv (a [^] k))"
      by (simp only: \<open>a' \<in> H\<close> \<open>x' \<in> H\<close> inv_closed m_closed H.mem_carrier m_ac nat_pow_closed a)
    also from a have "a' \<otimes> inv (a [^] k) = a [^] (int h - int k)"
      by (subst int_pow_diff) (auto simp: a'_def int_pow_int)
    also from \<open>k < h\<close> have "int h - int k = int (h - k)"
      by simp
    also have "a [^] \<dots> = a [^] (h - k)" 
      by (simp add: int_pow_int)
    finally have "inv x = inv x' \<otimes> inv a' \<otimes> a [^] (h - k)" .
    moreover have "h - k < h" using \<open>k < h\<close> and False by simp
    ultimately show ?thesis
      by (auto simp: adjoin_def h_def intro!: exI[of _ "inv x' \<otimes> inv a'"] exI[of _ "h - k"])
  qed
qed

lemma adjoin_id:
  assumes "subgroup H G" and a: "a \<in> H"
  shows   "adjoin G H a = H"
proof -
  interpret subgroup H G by fact
  show ?thesis
  proof safe
    fix x assume "x \<in> H"
    with assms show "x \<in> adjoin G H a"
      by (auto simp: adjoin_def intro!: exI[of _ x] exI[of _ 0] subgroup_indicator_pos)
  qed (insert a, auto simp: adjoin_def)
qed

lemma adjoined_in_adjoin:
  assumes "subgroup H G" and a: "a \<in> carrier G"
  shows   "a \<in> adjoin G H a"
proof (cases "a \<in> H")
  case True
  with assms show ?thesis by (subst adjoin_id) auto
next
  case False
  interpret subgroup H G by fact
  from assms have "subgroup_indicator G H a > 0" 
    by (intro subgroup_indicator_pos) auto
  moreover from False and assms and pow_subgroup_indicator[OF assms] 
    have "subgroup_indicator G H a \<noteq> 1" by (intro notI) auto
  ultimately have "subgroup_indicator G H a > 1" by simp
  with assms show ?thesis
    by (auto simp: adjoin_def intro!: exI[of _ \<one>] exI[of _ 1])
qed

lemma adjoin_subset:
  assumes "subgroup H G" and a: "a \<in> carrier G"
  shows   "adjoin G H a \<subseteq> carrier G"
proof -
  interpret subgroup H G by fact
  from a show ?thesis by (auto simp: adjoin_def)
qed

lemma inj_on_adjoin:
  assumes "subgroup H G" and a: "a \<in> carrier G" "a \<notin> H"
  defines "h \<equiv> subgroup_indicator G H a"
  shows   "inj_on (\<lambda>(x, k). x \<otimes> a [^] k) (H \<times> {..<h})"
proof (intro inj_onI, clarify, goal_cases)
  case (1 x k y l)
  interpret H: subgroup H G by fact
  have wf: "x \<in> carrier G" "y \<in> carrier G" "a [^] k \<in> carrier G" "a [^] l \<in> carrier G"
    using 1 a by auto
  have "x \<otimes> inv y = (x \<otimes> inv y) \<otimes> (a [^] k \<otimes> inv (a [^] k))"
    by (simp add: wf)
  also have "\<dots> = x \<otimes> a [^] k \<otimes> inv y \<otimes> inv (a [^] k)"
    by (simp only: m_ac wf inv_closed m_closed)
  also from a have "\<dots> = y \<otimes> a [^] l \<otimes> inv y \<otimes> inv (a [^] k)"
    by (subst 1) (simp_all)
  also have "\<dots> = y \<otimes> inv y \<otimes> (a [^] l \<otimes> inv (a [^] k))"
    by (simp only: m_ac wf inv_closed m_closed)
  also from wf have "\<dots> = a [^] int l \<otimes> inv (a [^] int k)"
    by (simp add: int_pow_int)
  also have "\<dots> = a [^] (int l - int k)"
    by (rule int_pow_diff [symmetric]) fact+
  finally have *: "x \<otimes> inv y = a [^] (int l - int k)" .

  have **: "a [^] (nat \<bar>int l - int k\<bar>) \<in> H"
  proof (cases "k \<le> l")
    case True
    from 1 have "a [^] (int l - int k) \<in> H" by (subst * [symmetric]) auto
    also have "a [^] (int l - int k) = a [^] (nat \<bar>int l - int k\<bar>)"
      using True by (simp add: nat_diff_distrib int_pow_int [symmetric] of_nat_diff)
    finally show ?thesis .
  next
    case False
    from 1 have "inv (a [^] (int l - int k)) \<in> H" by (subst * [symmetric]) auto
    also have "inv (a [^] (int l - int k)) = a [^] (nat \<bar>int l - int k\<bar>)" using False a 
      by (simp add: int_pow_neg [symmetric] nat_diff_distrib int_pow_int [symmetric] of_nat_diff)
    finally show ?thesis .
  qed
  have "k = l"
  proof (rule ccontr)
    assume "k \<noteq> l"
    with a and ** have "h \<le> nat \<bar>int l - int k\<bar>" unfolding h_def
      by (intro subgroup_indicator_le) auto
    also have "\<dots> < h" using \<open>l < h\<close> and \<open>k < h\<close> by linarith
    finally show False ..
  qed
  with 1 and a show ?case by simp
qed

lemma card_adjoin:
  assumes "subgroup H G" and a: "a \<in> carrier G" "a \<notin> H"
  shows   "card (adjoin G H a) = card H * subgroup_indicator G H a"
proof -
  interpret H: subgroup H G by fact
  define h where "h = subgroup_indicator G H a"
  have "adjoin G H a = (\<lambda>(x,k). x \<otimes> a [^] k) ` (H \<times> {..<h})"
    by (auto simp: adjoin_def h_def)
  also have "card \<dots> = card (H \<times> {..<h})" unfolding h_def
    by (intro card_image inj_on_adjoin assms)
  finally show ?thesis by (simp add: h_def card_cartesian_product)
qed

end

locale finite_comm_group_adjoin = finite_comm_group + subgroup H
  for H +
  fixes a :: 'a
  assumes a_in_carrier [simp]: "a \<in> carrier G"
  assumes a_notin_subgroup: "a \<notin> H"
begin

definition unadjoin :: "'a \<Rightarrow> 'a \<times> nat"  where
  "unadjoin x = 
     (THE z. z \<in> H \<times> {..<subgroup_indicator G H a} \<and> x = fst z \<otimes>\<^bsub>G\<^esub> a [^]\<^bsub>G\<^esub> snd z)"

lemma adjoin_unique:
  assumes "x \<in> adjoin G H a"
  defines "h \<equiv> subgroup_indicator G H a"
  shows   "\<exists>!z. z \<in> H \<times> {..<subgroup_indicator G H a} \<and> x = fst z \<otimes>\<^bsub>G\<^esub> a [^]\<^bsub>G\<^esub> snd z"
proof (rule ex_ex1I, goal_cases)
  case 1
  from assms show ?case by (auto simp: adjoin_def)
next
  case (2 z1 z2)
  have "subgroup H G" ..
  from inj_on_adjoin[OF this a_in_carrier a_notin_subgroup]
  show ?case by (rule inj_onD) (use 2 in auto)
qed

lemma unadjoin_correct:
  assumes "x \<in> adjoin G H a"
  shows   "fst (unadjoin x) \<in> H" and "snd (unadjoin x) < subgroup_indicator G H a"
          "fst (unadjoin x) \<otimes> a [^] snd (unadjoin x) = x"
  using theI'[OF adjoin_unique[OF assms], folded unadjoin_def] by auto

lemma unadjoin_unique:
  assumes "y \<in> H" "h < subgroup_indicator G H a"
  shows   "unadjoin (y \<otimes> a [^] h) = (y, h)"
proof -
  from assms have "y \<otimes> a [^] h \<in> adjoin G H a" by (auto simp: adjoin_def)
  note * = theI'[OF adjoin_unique[OF this], folded unadjoin_def]
  from inj_on_adjoin[OF is_subgroup a_in_carrier a_notin_subgroup] show ?thesis
    by (rule inj_onD) (insert * assms, auto)
qed

lemma unadjoin_unique':
  assumes "y \<in> H" "h < subgroup_indicator G H a" "x = y \<otimes> a [^] h"
  shows   "unadjoin x = (y, h)"
  using unadjoin_unique[OF assms(1,2)] assms(3) by simp

lemma unadjoin_1 [simp]: "unadjoin \<one> = (\<one>, 0)"
  by (intro unadjoin_unique') (auto intro!: subgroup_indicator_pos is_subgroup)

lemma unadjoin_in_base [simp]: "x \<in> H \<Longrightarrow> unadjoin x = (x, 0)"
  by (intro unadjoin_unique') (auto intro!: subgroup_indicator_pos is_subgroup)

lemma unadjoin_adjoined [simp]: "unadjoin a = (\<one>, 1)"
proof (rule unadjoin_unique')
  have "subgroup_indicator G H a \<noteq> 1" using is_subgroup a_notin_subgroup
    using pow_subgroup_indicator[of H a] by auto
  with subgroup_indicator_pos [OF is_subgroup a_in_carrier] 
    show "subgroup_indicator G H a > 1" by simp
qed auto

end


subsection \<open>Induction by adjoining elements\<close>

context finite_comm_group
begin

lemma group_decompose_adjoin_aux:
  assumes "subgroup H G"
  shows   "H = carrier G \<or> 
           (\<exists>H' a. H \<subseteq> H' \<and> subgroup H' G \<and> a \<in> carrier G - H' \<and> carrier G = adjoin G H' a)"
proof -
  have ind: "(\<And>H. subgroup H G \<Longrightarrow> H \<noteq> carrier G \<Longrightarrow> P (adjoin G H (SOME a. a \<in> carrier G - H))
                \<Longrightarrow> P H) \<Longrightarrow> (\<And>H. subgroup H G \<Longrightarrow> H = carrier G \<Longrightarrow> P H) \<Longrightarrow>
                (\<And>H. \<not> subgroup H G \<Longrightarrow> P H) \<Longrightarrow> P a0" for P a0
  proof (induction_schema, force, rule wf_bounded_set)
    fix H assume H: "subgroup H G" "H \<noteq> carrier G"
    interpret subgroup H G by fact
    from H have H': "H \<subset> carrier G" by auto
    define a where "a = (SOME a. a \<in> carrier G - H)"
    have a: "a \<in> carrier G - H" unfolding a_def
      by (rule someI_ex) (insert H', auto)  
    from a and H have "adjoin G H a \<subseteq> carrier G" by (intro adjoin_subset) auto
    from a and H have "a \<in> adjoin G H a" "a \<notin> H"
      by (auto simp: adjoined_in_adjoin)
    hence "adjoin G H a \<noteq> H" by blast
    with H and a show "(adjoin G H a, H) \<in> {(B,A). A \<subset> B \<and> B \<subseteq> carrier G}"
      using adjoin_subset[of H a] by (auto intro: mem_adjoin)
  next
    fix A B assume "(B, A) \<in> {(B, A). A \<subset> B \<and> B \<subseteq> carrier G}"
    thus "finite (carrier G) \<and> carrier G \<subseteq> carrier G \<and> B \<subseteq> carrier G \<and> A \<subset> B"
      by auto
  qed

  from assms show ?thesis
  proof (induction H rule: ind)
    case (1 H)
    interpret subgroup H G by fact
    define a where "a = (SOME a. a \<in> carrier G - H)"
    from "1.hyps" have "\<exists>a. a \<in> carrier G - H" by auto
    hence a: "a \<in> carrier G - H" unfolding a_def by (rule someI_ex)
  
    from "1.hyps" and a have "subgroup (adjoin G H a) G"
      by (intro adjoin_subgroup) auto
    from "1.IH"[folded a_def, OF this] 
      have "(\<exists>H' a. H \<subseteq> H' \<and> subgroup H' G \<and> a \<in> carrier G - H' \<and> carrier G = adjoin G H' a)"
    proof (elim disjE, goal_cases)
      case 1
      with a and \<open>subgroup H G\<close> show ?case
        by (intro exI[of _ H] exI[of _ a]) simp_all
    next
      case 2
      then obtain H' a' where *: "adjoin G H a \<subseteq> H'" "subgroup H' G" 
                                 "a' \<in> carrier G - H'" "carrier G = adjoin G H' a'" by blast
      thus ?case using mem_adjoin[OF \<open>subgroup H G\<close>, of _ a] a
        by (intro exI[of _ H'] exI[of _ a']) auto
    qed
    thus ?case by blast
  qed auto
qed

lemma group_decompose_adjoin:
  assumes "subgroup H0 G" "H0 \<noteq> carrier G"
  obtains H a where "H0 \<subseteq> H" "subgroup H G" "a \<in> carrier G - H" "carrier G = adjoin G H a"
proof -
  from group_decompose_adjoin_aux[OF assms(1)] and assms(2) and that show ?thesis by blast
qed

lemma subgroup_adjoin_induct [consumes 1, case_names base adjoin]:
  assumes "subgroup H0 G"
  assumes base: "P (G\<lparr>carrier := H0\<rparr>)"
  assumes adjoin: "\<And>H a. subgroup H G \<Longrightarrow> H0 \<subseteq> H \<Longrightarrow> a \<in> carrier G - H \<Longrightarrow> P (G\<lparr>carrier := H\<rparr>) \<Longrightarrow> 
                           P (G\<lparr>carrier := adjoin G H a\<rparr>)"
  shows   "P G"
proof -
  define H where "H = carrier G"
  have "finite H" by (auto simp: H_def fin)
  moreover have "subgroup H G" unfolding H_def by standard auto
  moreover {
    interpret subgroup H0 G by fact
    have "H0 \<subseteq> H" by (simp add: H_def subset)
  }
  ultimately have "P (G\<lparr>carrier := H\<rparr>)"
  proof (induction H rule: finite_psubset_induct)
    case (psubset H)
    show ?case
    proof (cases "H = H0")
      case True
      thus ?thesis by (simp add: base)
    next
      case False
      interpret H_sg: subgroup H G by fact
      interpret H: finite_comm_group "G\<lparr>carrier := H\<rparr>"
        by (rule subgroup_imp_finite_comm_group) fact
      have sg: "subgroup H0 (G\<lparr>carrier := H\<rparr>)"
        by (simp add: H_sg.subgroup_axioms \<open>subgroup H0 G\<close> psubset.prems(2) subgroup_incl)
      from H.group_decompose_adjoin[OF sg] and False
        obtain H' a where H': "H0 \<subseteq> H'" "subgroup H' (G\<lparr>carrier := H\<rparr>)" "a \<in> H - H'" 
                              "H = adjoin G H' a" by (auto simp: order_def)
      have "subgroup H' G"
        using \<open>subgroup H G\<close> and H'(2) group.incl_subgroup by blast
      from H' and adjoined_in_adjoin[of H' a] and \<open>subgroup H' G\<close> and mem_adjoin[of H' _ a]
        have "a \<in> H" and "a \<notin> H'" and "H' \<subseteq> H" by auto
      hence "H' \<subset> H" by blast
      from psubset.IH [OF \<open>H' \<subset> H\<close> \<open>subgroup H' G\<close> \<open>H0 \<subseteq> H'\<close>] have "P (G\<lparr>carrier := H'\<rparr>)" .
      with H' and \<open>subgroup H' G\<close> have "P (G\<lparr>carrier := adjoin G H' a\<rparr>)"
        by (intro adjoin) auto
      also from H' have "adjoin G H' a = H" by simp
      finally show ?thesis .
    qed
  qed
  thus "P G" by (simp add: H_def)
qed

lemma subgroup_adjoin_induct' [case_names singleton adjoin]:
  assumes singleton: "P (G\<lparr>carrier := {\<one>}\<rparr>)"
  assumes adjoin: "\<And>H a. subgroup H G \<Longrightarrow> a \<in> carrier G - H \<Longrightarrow> P (G\<lparr>carrier := H\<rparr>) \<Longrightarrow> 
                           P (G\<lparr>carrier := adjoin G H a\<rparr>)"
  shows   "P G"
proof -
  have "subgroup {\<one>} G" by standard auto
  from this and assms show ?thesis by (rule subgroup_adjoin_induct)
qed

end

end