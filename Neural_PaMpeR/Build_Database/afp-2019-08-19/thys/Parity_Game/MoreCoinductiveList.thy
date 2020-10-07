section \<open>Auxiliary Lemmas for Coinductive Lists\<close>

text \<open>Some lemmas to allow better reasoning with coinductive lists.\<close>

theory MoreCoinductiveList
imports
  Main
  Coinductive.Coinductive_List
begin

subsection \<open>@{term "lset"}\<close>

lemma lset_lnth: "x \<in> lset xs \<Longrightarrow> \<exists>n. lnth xs n = x"
  by (induct rule: llist.set_induct, meson lnth_0, meson lnth_Suc_LCons)

lemma lset_lnth_member: "\<lbrakk> lset xs \<subseteq> A; enat n < llength xs \<rbrakk> \<Longrightarrow> lnth xs n \<in> A"
  using contra_subsetD[of "lset xs" A] in_lset_conv_lnth[of _ xs] by blast

lemma lset_nth_member_inf: "\<lbrakk> \<not>lfinite xs; lset xs \<subseteq> A \<rbrakk> \<Longrightarrow> lnth xs n \<in> A"
  by (metis contra_subsetD inf_llist_lnth lset_inf_llist rangeI)

lemma lset_intersect_lnth: "lset xs \<inter> A \<noteq> {} \<Longrightarrow> \<exists>n. enat n < llength xs \<and> lnth xs n \<in> A"
  by (metis disjoint_iff_not_equal in_lset_conv_lnth)

lemma lset_ltake_Suc:
  assumes "\<not>lnull xs" "lnth xs 0 = x" "lset (ltake (enat n) (ltl xs)) \<subseteq> A"
  shows "lset (ltake (enat (Suc n)) xs) \<subseteq> insert x A"
proof-
  have "lset (ltake (eSuc (enat n)) (LCons x (ltl xs))) \<subseteq> insert x A"
    using assms(3) by auto
  moreover from assms(1,2) have "LCons x (ltl xs) = xs"
    by (metis lnth_0 ltl_simps(2) not_lnull_conv)
  ultimately show ?thesis by (simp add: eSuc_enat)
qed

lemma lfinite_lset: "lfinite xs \<Longrightarrow> \<not>lnull xs \<Longrightarrow> llast xs \<in> lset xs"
proof (induct rule: lfinite_induct)
  case (LCons xs)
  show ?case proof (cases)
    assume *: "\<not>lnull (ltl xs)"
    hence "llast (ltl xs) \<in> lset (ltl xs)" using LCons.hyps(3) by blast
    hence "llast (ltl xs) \<in> lset xs" by (simp add: in_lset_ltlD)
    thus ?thesis by (metis * LCons.prems lhd_LCons_ltl llast_LCons2)
  qed (metis LCons.prems lhd_LCons_ltl llast_LCons llist.set_sel(1))
qed simp

lemma lset_subset: "\<not>(lset xs \<subseteq> A) \<Longrightarrow> \<exists>n. enat n < llength xs \<and> lnth xs n \<notin> A"
  by (metis in_lset_conv_lnth subsetI)

subsection \<open>@{term "llength"}\<close>

lemma enat_Suc_ltl:
  assumes "enat (Suc n) < llength xs"
  shows "enat n < llength (ltl xs)"
proof-
  from assms have "eSuc (enat n) < llength xs" by (simp add: eSuc_enat)
  hence "enat n < epred (llength xs)" using eSuc_le_iff ileI1 by fastforce
  thus ?thesis by (simp add: epred_llength)
qed

lemma enat_ltl_Suc: "enat n < llength (ltl xs) \<Longrightarrow> enat (Suc n) < llength xs"
  by (metis eSuc_enat ldrop_ltl leD leI lnull_ldrop)

lemma infinite_small_llength [intro]: "\<not>lfinite xs \<Longrightarrow> enat n < llength xs"
  using enat_iless lfinite_conv_llength_enat neq_iff by blast

lemma lnull_0_llength: "\<not>lnull xs \<Longrightarrow> enat 0 < llength xs"
  using zero_enat_def by auto

lemma Suc_llength: "enat (Suc n) < llength xs \<Longrightarrow> enat n < llength xs"
  using dual_order.strict_trans enat_ord_simps(2) by blast

subsection \<open>@{term "ltake"}\<close>

lemma ltake_lnth: "ltake n xs = ltake n ys \<Longrightarrow> enat m < n \<Longrightarrow> lnth xs m = lnth ys m"
  by (metis lnth_ltake)

lemma lset_ltake_prefix [simp]: "n \<le> m \<Longrightarrow> lset (ltake n xs) \<subseteq> lset (ltake m xs)"
  by (simp add: lprefix_lsetD)

lemma lset_ltake: "(\<And>m. m < n \<Longrightarrow> lnth xs m \<in> A) \<Longrightarrow> lset (ltake (enat n) xs) \<subseteq> A"
proof (induct n arbitrary: xs)
  case 0
  have "ltake (enat 0) xs = LNil" by (simp add: zero_enat_def)
  thus ?case by simp
next
  case (Suc n)
  show ?case proof (cases)
    assume "xs \<noteq> LNil"
    then obtain x xs' where xs: "xs = LCons x xs'" by (meson neq_LNil_conv)
    { fix m assume "m < n"
      hence "Suc m < Suc n" by simp
      hence "lnth xs (Suc m) \<in> A" using Suc.prems by presburger
      hence "lnth xs' m \<in> A" using xs by simp
    }
    hence "lset (ltake (enat n) xs') \<subseteq> A" using Suc.hyps by blast
    moreover have "ltake (enat (Suc n)) xs = LCons x (ltake (enat n) xs')"
      using xs ltake_eSuc_LCons[of _ x xs'] by (metis (no_types) eSuc_enat)
    moreover have "x \<in> A" using Suc.prems xs by force
    ultimately show ?thesis by simp
  qed simp
qed

lemma llength_ltake': "enat n < llength xs \<Longrightarrow> llength (ltake (enat n) xs) = enat n"
  by (metis llength_ltake min.strict_order_iff)

lemma llast_ltake:
  assumes "enat (Suc n) < llength xs"
  shows "llast (ltake (enat (Suc n)) xs) = lnth xs n" (is "llast ?A = _")
  unfolding llast_def using llength_ltake'[OF assms] by (auto simp add: lnth_ltake)

lemma lset_ltake_ltl: "lset (ltake (enat n) (ltl xs)) \<subseteq> lset (ltake (enat (Suc n)) xs)"
proof (cases)
  assume "\<not>lnull xs"
  then obtain v0 where "xs = LCons v0 (ltl xs)" by (metis lhd_LCons_ltl)
  hence "ltake (eSuc (enat n)) xs = LCons v0 (ltake (enat n) (ltl xs))"
    by (metis ltake_eSuc_LCons)
  hence "lset (ltake (enat (Suc n)) xs) = lset (LCons v0 (ltake (enat n) (ltl xs)))"
    by (simp add: eSuc_enat)
  thus ?thesis using lset_LCons[of v0 "ltake (enat n) (ltl xs)"] by blast
qed (simp add: lnull_def)

subsection \<open>@{term "ldropn"}\<close>

lemma ltl_ldrop: "\<lbrakk> \<And>xs. P xs \<Longrightarrow> P (ltl xs); P xs \<rbrakk> \<Longrightarrow> P (ldropn n xs)"
  unfolding ldropn_def by (induct n) simp_all

subsection \<open>@{term "lfinite"}\<close>

lemma lfinite_drop_set: "lfinite xs \<Longrightarrow> \<exists>n. v \<notin> lset (ldrop n xs)"
  by (metis ldrop_inf lmember_code(1) lset_lmember)

lemma index_infinite_set:
  "\<lbrakk> \<not>lfinite x; lnth x m = y; \<And>i. lnth x i = y \<Longrightarrow> (\<exists>m > i. lnth x m = y) \<rbrakk> \<Longrightarrow> y \<in> lset (ldropn n x)"
proof (induct n arbitrary: x m)
  case 0 thus ?case using lset_nth_member_inf by auto
next
  case (Suc n)
  obtain a xs where x: "x = LCons a xs" by (meson Suc.prems(1) lnull_imp_lfinite not_lnull_conv)
  obtain j where j: "j > m" "lnth x j = y" using Suc.prems(2,3) by blast
  have "lnth xs (j - 1) = y" by (metis lnth_LCons' j(1,2) not_less0 x)
  moreover {
    fix i assume "lnth xs i = y"
    hence "lnth x (Suc i) = y" by (simp add: x)
    hence "\<exists>j>i. lnth xs j = y" by (metis Suc.prems(3) Suc_lessE lnth_Suc_LCons x)
  }
  ultimately show ?case using Suc.hyps Suc.prems(1) x by auto
qed

subsection \<open>@{term "lmap"}\<close>

lemma lnth_lmap_ldropn:
  "enat n < llength xs \<Longrightarrow> lnth (lmap f (ldropn n xs)) 0 = lnth (lmap f xs) n"
  by (simp add: lhd_ldropn lnth_0_conv_lhd)

lemma lnth_lmap_ldropn_Suc:
  "enat (Suc n) < llength xs \<Longrightarrow> lnth (lmap f (ldropn n xs)) (Suc 0) = lnth (lmap f xs) (Suc n)"
  by (metis (no_types, lifting) Suc_llength ldropn_ltl leD llist.map_disc_iff lnth_lmap_ldropn
                                lnth_ltl lnull_ldropn ltl_ldropn ltl_lmap)

subsection \<open>Notation\<close>

text \<open>We introduce the notation \$ to denote @{term "lnth"}.\<close>

notation lnth (infix "$" 61)

end
