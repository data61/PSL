section \<open>Correctness\<close>

subsection \<open>Well-formed queries\<close>

theory Generic_Join_Correctness
  imports Generic_Join
begin

definition wf_set :: "nat \<Rightarrow> vertices \<Rightarrow> bool" where
  "wf_set n V \<longleftrightarrow> (\<forall>x\<in>V. x < n)"

definition wf_atable :: "nat \<Rightarrow> 'a atable \<Rightarrow> bool" where
  "wf_atable n X \<longleftrightarrow> table n (fst X) (snd X) \<and> finite (fst X)"

definition wf_query :: "nat \<Rightarrow> vertices \<Rightarrow> 'a query \<Rightarrow> 'a query \<Rightarrow> bool" where
  "wf_query n V Q_pos Q_neg \<longleftrightarrow> (\<forall>X\<in>(Q_pos \<union> Q_neg). wf_atable n X) \<and> (wf_set n V) \<and> (card Q_pos \<ge> 1)"

definition included :: "vertices \<Rightarrow> 'a query \<Rightarrow> bool" where
  "included V Q \<longleftrightarrow> (\<forall>(S, X)\<in>Q. S \<subseteq> V)"

definition covering :: "vertices \<Rightarrow> 'a query \<Rightarrow> bool" where
  "covering V Q \<longleftrightarrow> V \<subseteq> (\<Union>(S, X)\<in>Q. S)"

definition non_empty_query :: "'a query \<Rightarrow> bool" where
  "non_empty_query Q = (\<forall>X\<in>Q. card (fst X) \<ge> 1)"

definition rwf_query :: "nat \<Rightarrow> vertices \<Rightarrow> 'a query \<Rightarrow> 'a query \<Rightarrow> bool" where
  "rwf_query n V Qp Qn \<longleftrightarrow> wf_query n V Qp Qn \<and> covering V Qp \<and> included V Qp \<and> included V Qn
                         \<and> non_empty_query Qp \<and> non_empty_query Qn"

lemma wf_tuple_empty: "wf_tuple n {} v \<longleftrightarrow> v = replicate n None"
  by (auto intro!: replicate_eqI simp add: wf_tuple_def in_set_conv_nth)

lemma table_empty: "table n {} X \<longleftrightarrow> (X = empty_table \<or> X = unit_table n)"
  by (auto simp add: wf_tuple_empty unit_table_def table_def)

context getIJ begin

lemma isSame_equi_dev:
  assumes "wf_set n V"
  assumes "wf_tuple n A t1"
  assumes "wf_tuple n B t2"
  assumes "s \<subseteq> A"
  assumes "s \<subseteq> B"
  assumes "A \<subseteq> V"
  assumes "B \<subseteq> V"
  shows "isSameIntersection t1 s t2 = (restrict s t1 = restrict s t2)"
proof -
  have "(\<forall>i\<in>s. t1!i = t2!i) \<longleftrightarrow> (restrict s t1 = restrict s t2)" (is "?A \<longleftrightarrow> ?B")
  proof -
    have "?B \<Longrightarrow> ?A"
    proof -
      assume "?B"
      have "\<And>i. i\<in>s \<Longrightarrow> t1!i = t2!i"
      proof -
        fix i assume "i \<in> s"
        then have "i \<in> A" using assms(4) by blast
        then have "i < n" using assms(1) assms(6) wf_set_def by auto
        then show "t1!i = t2!i" by (metis (no_types, lifting) \<open>i \<in> s\<close> \<open>restrict s t1 = restrict s t2\<close>
              assms(2) length_restrict nth_restrict wf_tuple_length)
      qed
      then show "?A" by blast
    qed
    moreover have "?A \<Longrightarrow> ?B"
    proof -
      assume "?A"
      obtain "length (restrict s t1) = n" "length (restrict s t2) = n"
        using assms(2) assms(3) length_restrict wf_tuple_length by blast
      then have "\<And>i. i < n \<Longrightarrow> (restrict s t1)!i = (restrict s t2)!i"
      proof -
        fix i assume "i < n"
        then show "(restrict s t1)!i = (restrict s t2)!i"
        proof (cases "i \<in> s")
          case True
          then show ?thesis by (metis \<open>\<forall>i\<in>s. t1 ! i = t2 ! i\<close> \<open>i < n\<close> \<open>length (restrict s t1) = n\<close>
                \<open>length (restrict s t2) = n\<close> length_restrict nth_restrict)
        next
          case False
          then show ?thesis
            by (metis (no_types, hide_lams) \<open>i < n\<close> assms(2) assms(3) assms(4) assms(5) wf_tuple_def
                wf_tuple_restrict_simple)
        qed
      qed
      then show "?B"
        by (metis \<open>length (restrict s t1) = n\<close> \<open>length (restrict s t2) = n\<close> nth_equalityI)
    qed
    then show ?thesis using calculation by linarith
  qed
  then show ?thesis by simp
qed

lemma wf_getIJ:
  assumes "card V \<ge> 2"
  assumes "wf_set n V"
  assumes "(I, J) = getIJ Q_pos Q_neg V"
  shows "wf_set n I" and "wf_set n J"
  using assms unfolding wf_set_def by (metis Un_iff coreProperties)+

lemma wf_projectTable:
  assumes "wf_atable n X"
  shows "wf_atable n (projectTable I X) \<and> (fst (projectTable I X) = (fst X \<inter> I))"
proof -
  obtain Y where "Y = projectTable I X" by simp
  obtain sX tX where "(sX, tX) = X" by (metis surj_pair)
  moreover obtain S where "S = I \<inter> sX" by simp
  moreover obtain sY tY where "(sY, tY) = Y" by (metis surj_pair)
  then have "sY = S"
    using calculation(1) calculation(2) \<open>Y = projectTable I X\<close> by auto
  then have "\<And>t. t \<in> tY \<Longrightarrow> wf_tuple n S t"
  proof -
    fix t assume "t \<in> tY"
    obtain x where "x \<in> tX" "t = restrict I x" using \<open>(sY, tY) = Y\<close> \<open>t \<in> tY\<close> \<open>Y = projectTable I X\<close> calculation(1) by auto
    then have "wf_tuple n sX x"
    proof -
      have "table n sX tX" using assms(1) calculation(1) wf_atable_def by fastforce
      then show ?thesis using \<open>x \<in> tX\<close> table_def by blast
    qed
    then show "wf_tuple n S t" using \<open>t = restrict I x\<close> calculation(2) wf_tuple_restrict by blast      
  qed
  then have "\<forall>t \<in> tY. wf_tuple n S t" by blast
  then have "table n S tY" using table_def by blast
  then show ?thesis
    by (metis \<open>(sY, tY) = Y\<close> \<open>Y = projectTable I X\<close> \<open>sY = S\<close> assms calculation(1) calculation(2) finite_Int fst_conv inf_commute snd_conv wf_atable_def)
qed

lemma set_filterQuery:
  assumes "QQ = filterQuery I Q"
  assumes "non_empty_query Q"
  shows "\<forall>X\<in>Q. (card (fst X \<inter> I) \<ge> 1 \<longleftrightarrow> X \<in> QQ)"
proof -
  have "\<And>X. X \<in> Q \<Longrightarrow> (card (fst X \<inter> I) \<ge> 1 \<longleftrightarrow> X \<in> QQ)"
  proof -
    fix X assume "X \<in> Q"
    have "card (fst X \<inter> I) \<ge> 1 \<Longrightarrow> X \<in> QQ"
    proof -
      assume "card (fst X \<inter> I) \<ge> 1"
      then have "(\<lambda>(s, _). s \<inter> I \<noteq> {}) X" by force
      then show ?thesis by (simp add: \<open>case X of (s, uu_) \<Rightarrow> s \<inter> I \<noteq> {}\<close> Set.is_empty_def \<open>X \<in> Q\<close> assms(1))        
    qed
    moreover have "X \<in> QQ \<Longrightarrow> card (fst X \<inter> I) \<ge> 1"
    proof -
      assume "X \<in> QQ"
      have "(\<lambda>(s, _). s \<inter> I \<noteq> {}) X" using Set.is_empty_def \<open>X \<in> QQ\<close> assms(1) by auto
      then have "fst X \<inter> I \<noteq> {}" by (simp add: case_prod_beta')
      then show ?thesis
        by (metis One_nat_def Suc_leI \<open>X \<in> Q\<close> assms(2) card.infinite card_gt_0_iff finite_Int non_empty_query_def)
    qed
    then show "(card (fst X \<inter> I) \<ge> 1 \<longleftrightarrow> X \<in> QQ)"
      using calculation by blast
  qed
  then show ?thesis by blast
qed

lemma wf_filterQuery:
  assumes "I \<subseteq> V"
  assumes "card I \<ge> 1"
  assumes "rwf_query n V Qp Qn"
  assumes "QQp = filterQuery I Qp"
  assumes "QQn = filterQueryNeg I Qn"
  shows "wf_query n I QQp QQn" "non_empty_query QQp" "covering I QQp"
proof -
  show "non_empty_query QQp"
    by (metis assms(3) assms(4) filterQuery.simps member_filter non_empty_query_def rwf_query_def)
  show "covering I QQp"
  proof -
    have "\<forall>X\<in>Qp. (card (fst X \<inter> I) \<ge> 1 \<longleftrightarrow> X \<in> QQp)"
      using set_filterQuery assms(3) assms(4) rwf_query_def by fastforce
    have "(\<Union>(S, X)\<in>Qp. S) \<inter> I \<subseteq> (\<Union>(S, _)\<in>QQp. S)" (is "?A \<inter> I \<subseteq> ?B")
    proof (rule subsetI)
      fix x assume "x \<in> ?A \<inter> I"
      have "x \<in> ?A" using \<open>x \<in> (\<Union>(S, X)\<in>Qp. S) \<inter> I\<close> by blast
      then obtain S X where "(S, X) \<in> Qp" and "x \<in> S" by blast
      moreover have "(S, X) \<in> QQp" by (metis Int_iff One_nat_def Suc_le_eq
            \<open>\<forall>X\<in>Qp. (1 \<le> card (fst X \<inter> I)) = (X \<in> QQp)\<close> \<open>x \<in> (\<Union>(S, X)\<in>Qp. S) \<inter> I\<close> assms(2)
            calculation(1) calculation(2) card_gt_0_iff empty_iff finite_Int fst_conv)
      ultimately show "x \<in> ?B" by auto
    qed
    then show ?thesis
      by (metis (mono_tags, lifting) assms(1) assms(3) covering_def inf.absorb_iff2 le_infI1 rwf_query_def)
  qed
  show "wf_query n I QQp QQn"
  proof -
    have "(\<forall>X\<in>QQp. wf_atable n X)"
      using assms(3) assms(4) rwf_query_def wf_query_def by fastforce
    moreover have "(wf_set n I)"
      by (meson assms(1) assms(3) rwf_query_def subsetD wf_query_def wf_set_def)
    moreover have "card QQp \<ge> 1"
    proof -
      have "covering I QQp" by (simp add: \<open>covering I QQp\<close>)
      have "\<not> (Set.is_empty QQp)"
      proof (rule ccontr)
        assume "\<not> (\<not> (Set.is_empty QQp))"
        have "Set.is_empty QQp" using \<open>\<not> \<not> Set.is_empty QQp\<close> by auto
        have "(\<Union>(S, X)\<in>QQp. S) = {}" by (metis SUP_empty Set.is_empty_def \<open>Set.is_empty QQp\<close>)
        then show "False"
          by (metis \<open>covering I QQp\<close> assms(2) card_eq_0_iff covering_def not_one_le_zero subset_empty)
      qed
      moreover have "finite QQp"
        by (metis assms(3) assms(4) card_infinite filterQuery.simps finite_filter not_one_le_zero rwf_query_def wf_query_def)
      then show ?thesis
        by (metis One_nat_def Set.is_empty_def Suc_leI calculation card_gt_0_iff)
    qed
    moreover have "QQn \<subseteq> Qn"
    proof -
      have "QQn = filterQueryNeg I Qn" by (simp add: assms(5))
      then show ?thesis by auto
    qed
    moreover have "wf_query n I QQp Qn"
      by (meson Un_iff assms(3) calculation(1) calculation(2) calculation(3) rwf_query_def wf_query_def)
    then have "(\<forall>X\<in>Qn. wf_atable n X)" by (simp add: wf_query_def)
    then show ?thesis 
      by (meson \<open>wf_query n I QQp Qn\<close> calculation(4) subset_eq sup_mono wf_query_def)
  qed
qed

lemma wf_set_subset:
  assumes "I \<subseteq> V"
  assumes "card I \<ge> 1"
  assumes "wf_set n V"
  shows "wf_set n I"
  using assms(1) assms(3) wf_set_def by auto

lemma wf_projectQuery:
  assumes "card I \<ge> 1"
  assumes "wf_query n I Q Qn"
  assumes "non_empty_query Q"
  assumes "covering I Q"
  assumes "\<forall>X\<in>Q. card (fst X \<inter> I) \<ge> 1"
  assumes "QQ = projectQuery I Q"
  assumes "included I Qn"
  assumes "non_empty_query Qn"
  shows "rwf_query n I QQ Qn"
proof -
  have "wf_query n I QQ Qn"
  proof -
    have "\<forall>X\<in>QQ. wf_atable n X" using assms(2) assms(6) wf_query_def
      by (simp add: wf_projectTable wf_query_def)
    moreover have "wf_set n I" using assms(2) wf_query_def by blast
    moreover have "card QQ \<ge> 1"
    proof -
      have "card QQ = card (Set.image (projectTable I) Q)" by (simp add: assms(6))
      then show ?thesis
        by (metis One_nat_def Suc_le_eq assms(2) card_gt_0_iff finite_imageI image_is_empty wf_query_def)
    qed
    then show ?thesis by (metis Un_iff assms(2) calculation(1) wf_query_def)
  qed
  moreover have "covering I QQ"
  proof -
    have "I \<subseteq> (\<Union>(S, X)\<in>Q. S)" using assms(4) covering_def by auto
    moreover have "(\<Union>(S, X)\<in>Q. S \<inter> I) \<subseteq> (\<Union>(S, X)\<in>QQ. S)"
    proof (rule subsetI)
      fix x assume "x \<in> (\<Union>(S, X)\<in>Q. S \<inter> I)"
      obtain S X where "(S, X) \<in> Q" and "x \<in> S \<inter> I" using \<open>x \<in> (\<Union>(S, X)\<in>Q. S \<inter> I)\<close> by blast
      then have "fst (projectTable I (S, X)) = S \<inter> I" by simp
      have "wf_atable n (S, X)" using \<open>(S, X) \<in> Q\<close> assms(2) wf_query_def by blast
      then have "wf_atable n (projectTable I (S, X))" using wf_projectTable by blast 
      then show "x \<in> (\<Union>(S, X)\<in>QQ. S)" using \<open>(S, X) \<in> Q\<close> \<open>x \<in> S \<inter> I\<close> assms(6) by fastforce
    qed
    moreover have "(\<Union>(S, X)\<in>Q. S \<inter> I) = (\<Union>(S, X)\<in>Q. S) \<inter> I" by blast
    then show ?thesis using calculation(1) calculation(2) covering_def inf_absorb2 by fastforce
  qed
  moreover have "included I QQ"
  proof -
    have "\<And>S X. (S, X) \<in> QQ \<Longrightarrow> S \<subseteq> I"
    proof -
      fix S X assume "(S, X) \<in> QQ"
      have "(S, X) \<in> Set.image (projectTable I) Q" using \<open>(S, X) \<in> QQ\<close> assms(6) by simp
      obtain XX where "XX \<in> Q" and "(S, X) = projectTable I XX" using \<open>(S, X) \<in> projectTable I ` Q\<close> by blast
      then have "S = I \<inter> (fst XX)"
        by (metis projectTable.simps fst_conv inf_commute prod.collapse)
      then show "S \<subseteq> I" by simp
    qed
    then have "(\<forall>(S, X)\<in>QQ. S \<subseteq> I)" by blast
    then show ?thesis by (simp add: included_def)
  qed
  moreover have "non_empty_query QQ" using assms(5) assms(6) non_empty_query_def by fastforce
  then show ?thesis
    by (simp add: assms(7) assms(8) calculation(1) calculation(2) calculation(3) rwf_query_def)
qed

lemma wf_firstRecursiveCall:
  assumes "rwf_query n V Qp Qn"
  assumes "card V \<ge> 2"
  assumes "(I, J) = getIJ Qp Qn V"
  assumes "Q_I_pos = projectQuery I (filterQuery I Qp)"
  assumes "Q_I_neg = filterQueryNeg I Qn"
  shows "rwf_query n I Q_I_pos Q_I_neg"
proof -
  obtain "I \<subseteq> V" "card I \<ge> 1" using assms(2) assms(3) getIJProperties(5) getIJProperties(1) by fastforce
  define tQ where "tQ = filterQuery I Qp"
  obtain "wf_query n I tQ Q_I_neg" "non_empty_query tQ" "covering I tQ"
    by (metis wf_filterQuery(1) wf_filterQuery(2) wf_filterQuery(3)
        \<open>1 \<le> card I\<close> \<open>I \<subseteq> V\<close> assms(1) assms(5) tQ_def)
  moreover obtain "card I \<ge> 1" and "\<forall>X\<in>tQ. card (fst X \<inter> I) \<ge> 1"
    using set_filterQuery \<open>1 \<le> card I\<close> assms(1) rwf_query_def tQ_def by fastforce
  moreover have "included I Q_I_neg" by (simp add: assms(5) included_def)
  then show ?thesis
    by (metis wf_projectQuery \<open>\<And>thesis. (\<lbrakk>wf_query n I tQ Q_I_neg; non_empty_query tQ; covering I tQ\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
        assms(1) assms(4) assms(5) calculation(4) calculation(5) filterQueryNeg.simps member_filter non_empty_query_def rwf_query_def tQ_def)
qed

lemma wf_atable_subset:
  assumes "table n V X"
  assumes "Y \<subseteq> X"
  shows "table n V Y"
  by (meson assms(1) assms(2) subsetD table_def)

lemma same_set_semiJoin:
  "fst (semiJoin x other) = fst x"
proof -
  obtain sx tx where "x = (sx, tx)" by (metis surj_pair)
  obtain so to where "other = (so, to)" by (metis surj_pair)
  then show ?thesis by (simp add: \<open>x = (sx, tx)\<close>)
qed

lemma wf_semiJoin:
  assumes "card J \<ge> 1"
  assumes "wf_query n J Q Qn"
  assumes "non_empty_query Q"
  assumes "covering J Q"
  assumes "\<forall>X\<in>Q. card (fst X \<inter> J) \<ge> 1"
  assumes "QQ = (Set.image (\<lambda>tab. semiJoin tab (st, t)) Q)"
  shows "wf_query n J QQ Qn" "non_empty_query QQ" "covering J QQ"
proof -
  show "wf_query n J QQ Qn"
  proof -
    have "\<forall>X\<in>QQ. wf_atable n X"
    proof -
      have "\<And>X. X\<in>QQ \<Longrightarrow> wf_atable n X"
      proof -
        fix X assume "X \<in> QQ"
        obtain Y where "Y \<in> Q" and "X = semiJoin Y (st, t)" using \<open>X \<in> QQ\<close> assms(6) by blast
        then have "wf_atable n Y" using assms(2) wf_query_def by blast
        then show "wf_atable n X"
        proof -
          have "fst X = fst Y"
            by (metis \<open>X = semiJoin Y (st, t)\<close> fst_conv prod.collapse semiJoin.simps)
          moreover have "snd X \<subseteq> snd Y"
            by (metis \<open>X = semiJoin Y (st, t)\<close> member_filter prod.collapse semiJoin.simps snd_conv subsetI)
          then have "table n (fst X) (snd X)" by (metis \<open>wf_atable n Y\<close> calculation wf_atable_def wf_atable_subset)
          moreover have "finite (fst X)" by (metis \<open>wf_atable n Y\<close> calculation(1) wf_atable_def)
          then show ?thesis by (simp add: calculation(2) wf_atable_def)
        qed
      qed
      then show ?thesis by blast
    qed
    moreover have "wf_set n J" using assms(2) wf_query_def by blast
    moreover have "card QQ \<ge> 1"
      by (metis One_nat_def Suc_leI assms(2) assms(6) card.infinite card_gt_0_iff finite_imageI image_is_empty wf_query_def)
    then show ?thesis using calculation(1) calculation(2) wf_query_def Un_iff assms(2) by metis
  qed
  show "non_empty_query QQ"
    by (metis (no_types, lifting) assms(3) assms(6) image_iff non_empty_query_def same_set_semiJoin)
  show "covering J QQ"
  proof -
    have "(\<Union>(S, X)\<in>Q. S) = (\<Union>(S, X)\<in>QQ. S)" using assms(6) same_set_semiJoin by auto
    then show ?thesis by (metis assms(4) covering_def)
  qed
qed

lemma newQuery_equiv_def:
  "newQuery V Q (st, t) = projectQuery V (Set.image (\<lambda>tab. semiJoin tab (st, t)) Q)"
  by (metis image_image newQuery.simps projectQuery.elims)

lemma included_project:
  "included V (projectQuery V Q)"
proof -
  have "\<And>S X. (S, X)\<in>(projectQuery V Q) \<Longrightarrow> S \<subseteq> V"
  proof -
    fix S X assume "(S, X)\<in>(projectQuery V Q)"
    obtain SS XX where "(S, X) = projectTable V (SS, XX)"
      using \<open>(S, X) \<in> projectQuery V Q\<close> by auto
    then have "S = SS \<inter> V" by auto
    then show "S \<subseteq> V" by simp
  qed
  then show ?thesis by (metis case_prodI2 included_def)
qed

lemma non_empty_newQuery:
  assumes "Q1 = filterQuery J Q0"
  assumes "Q2 = newQuery J Q1 (I, t)"
  assumes "\<forall>X\<in>Q0. wf_atable n X"
  shows "non_empty_query Q2"
proof -
  have "\<And>X. X\<in>Q2 \<Longrightarrow> card (fst X) \<ge> 1"
  proof -
    fix X assume "X \<in> Q2"
    obtain X2 where "X = projectTable J X2" and "X2 \<in> Set.image (\<lambda>tab. semiJoin tab (I, t)) Q1"
      by (metis (mono_tags, lifting) newQuery.simps \<open>X \<in> Q2\<close> assms(2) image_iff)
    then have "card (fst X2 \<inter> J) \<ge> 1"
    proof -
      obtain X1 where "X1 \<in> Q1" and "X2 = semiJoin X1 (I, t)"
        using \<open>X2 \<in> (\<lambda>tab. semiJoin tab (I, t)) ` Q1\<close> by blast
      then have "fst X1 = fst X2" by (simp add: same_set_semiJoin)
      moreover have "X1 \<in> filterQuery J Q0" using \<open>X1 \<in> Q1\<close> assms(1) by blast
      then have "(\<lambda>(s, _). s \<inter> J \<noteq> {}) X1" using Set.is_empty_def by auto
      then have "\<not> (Set.is_empty (fst X1 \<inter> J))" by (simp add: Set.is_empty_def case_prod_beta')
      then show ?thesis
        by (metis filterQuery.elims One_nat_def Set.is_empty_def Suc_leI \<open>X1 \<in> Q1\<close> assms(1)
            assms(3) calculation card_gt_0_iff finite_Int member_filter wf_atable_def)
    qed
    then show "card (fst X) \<ge> 1"
      by (metis projectTable.simps \<open>X = projectTable J X2\<close> fst_conv prod.collapse)
  qed
  then show ?thesis by (simp add: non_empty_query_def)
qed

lemma wf_newQuery:
  assumes "card J \<ge> 1"
  assumes "wf_query n J Q Qn0"
  assumes "non_empty_query Q"
  assumes "covering J Q"
  assumes "\<forall>X\<in>Q. card (fst X \<inter> J) \<ge> 1"
  assumes "QQ = newQuery J Q t"
  assumes "QQn = newQuery J Qn t"
  assumes "non_empty_query Qn"
  assumes "Qn = filterQuery J Qn0"
  shows "rwf_query n J QQ QQn"
proof -
  obtain tt st where "(st, tt) = t" by (metis surj_pair)
  have "QQ = projectQuery J (Set.image (\<lambda>tab. semiJoin tab (st, tt)) Q)"
    by (metis \<open>(st, tt) = t\<close> assms(6) newQuery_equiv_def)
  define QS where "QS = Set.image (\<lambda>tab. semiJoin tab (st, tt)) Q"
  obtain "wf_query n J QS Qn0" "non_empty_query QS" "covering J QS"
    by (metis wf_semiJoin(1) wf_semiJoin(2) wf_semiJoin(3) QS_def
        assms(1) assms(2) assms(3) assms(4) assms(5))
  moreover have "\<forall>X\<in>QS. card (fst X \<inter> J) \<ge> 1" using QS_def assms(5) by auto
  then have "\<forall>X\<in>(projectQuery J QS). wf_atable n X"
    by (metis (no_types, lifting) projectQuery.simps Un_iff calculation(1) image_iff
        wf_projectTable wf_query_def)
  then have "wf_query n J QQ QQn"
  proof -
    have "\<And>X. X\<in>QQn \<Longrightarrow> wf_atable n X"
    proof -
      fix X assume "X \<in> QQn"
      have "QQn = projectQuery J (Set.image (\<lambda>tab. semiJoin tab (st, tt)) Qn)"
        using newQuery_equiv_def \<open>(st, tt) = t\<close> assms(7) by blast
      then obtain XX where "X = projectTable J XX" "XX \<in> (Set.image (\<lambda>tab. semiJoin tab (st, tt)) Qn)"
        using \<open>X \<in> QQn\<close> by auto
      then obtain XXX where "XX = semiJoin XXX (st, tt)" "XXX \<in> Qn" by blast
      then have "wf_atable n XXX"
        by (metis filterQuery.elims Un_iff assms(2) assms(9) member_filter wf_query_def)
      then have "wf_atable n XX"
      proof -
        have "fst XX = fst XXX"
          by (simp add: same_set_semiJoin \<open>XX = semiJoin XXX (st, tt)\<close>)
        moreover have "snd XX = Set.filter (isSameIntersection tt (fst XX \<inter> st)) (snd XXX)"
          by (metis semiJoin.simps \<open>XX = semiJoin XXX (st, tt)\<close> calculation prod.collapse snd_conv)
        moreover have "snd XX \<subseteq> snd XXX" using calculation(2) by auto
        then show ?thesis
          by (metis wf_atable_subset \<open>wf_atable n XXX\<close> calculation(1) wf_atable_def)
      qed
      then show "wf_atable n X" by (simp add: wf_projectTable \<open>X = projectTable J XX\<close>)
    qed
    then have "\<forall>X\<in>QQn. wf_atable n X" by blast
    then have "\<forall>X\<in>(QQ \<union> QQn). wf_atable n X"
      using QS_def \<open>QQ = projectQuery J ((\<lambda>tab. semiJoin tab (st, tt)) ` Q)\<close> \<open>\<forall>X\<in>projectQuery J QS. wf_atable n X\<close> by blast
    moreover have "card QQ \<ge> 1"
      by (metis (no_types, lifting) newQuery.simps One_nat_def Suc_leI \<open>(st, tt) = t\<close> assms(2)
          assms(6) card.infinite card_gt_0_iff finite_imageI image_is_empty wf_query_def)
    then show ?thesis using assms(2) calculation wf_query_def by blast
  qed
  moreover have "included J QQn"
  proof -
    have "QQn = projectQuery J (Set.image (\<lambda>tab. semiJoin tab (st, tt)) Qn)"
      using newQuery_equiv_def \<open>(st, tt) = t\<close> assms(7) by blast
    then show ?thesis using included_project by blast
  qed
  moreover have "covering J QQ"
  proof -
    have "QQ = projectQuery J ((\<lambda>tab. semiJoin tab (st, tt)) `Q)"
      using \<open>QQ = projectQuery J ((\<lambda>tab. semiJoin tab (st, tt)) ` Q)\<close> by blast
    then have "covering J ((\<lambda>tab. semiJoin tab (st, tt)) `Q)" using QS_def calculation(3) by blast
    then have "J \<subseteq> (\<Union>(S, X)\<in>(((\<lambda>tab. semiJoin tab (st, tt)) `Q)). S)"
      by (simp add: covering_def)
    then have "J \<subseteq> (\<Union>(S, X)\<in>(((\<lambda>tab. semiJoin tab (st, tt)) `Q)). S) \<inter> J" by blast
    moreover have "(\<Union>(S, X)\<in>(((\<lambda>tab. semiJoin tab (st, tt)) `Q)). S) \<inter> J  \<subseteq> (\<Union>(S, X)\<in>(((\<lambda>tab. semiJoin tab (st, tt)) `Q)). S \<inter> J)"
      using image_cong by auto
    then have "(\<Union>(S, X)\<in>((\<lambda>tab. semiJoin tab (st, tt)) `Q). S) \<inter> J  \<subseteq> (\<Union>(S, X)\<in>(projectQuery J ((\<lambda>tab. semiJoin tab (st, tt)) `Q)). S)"
      by auto
    then show ?thesis
      by (metis \<open>J \<subseteq> (\<Union>(S, X)\<in>(\<lambda>tab. semiJoin tab (st, tt)) ` Q. S)\<close> \<open>QQ = projectQuery J ((\<lambda>tab. semiJoin tab (st, tt)) ` Q)\<close> covering_def inf_absorb2)
  qed
  moreover have "non_empty_query QQ" using QS_def \<open>QQ = projectQuery J ((\<lambda>tab. semiJoin tab (st, tt)) ` Q)\<close>
      \<open>\<forall>X\<in>QS. 1 \<le> card (fst X \<inter> J)\<close> non_empty_query_def by fastforce
  moreover have "non_empty_query QQn"
    by (metis non_empty_newQuery Un_iff \<open>(st, tt) = t\<close> assms(7) assms(9) calculation(1) wf_query_def)
  then show ?thesis
    using included_project \<open>QQ = projectQuery J ((\<lambda>tab. semiJoin tab (st, tt)) ` Q)\<close>
      calculation(4) calculation(5) calculation(6) calculation(7) rwf_query_def by blast
qed

lemma subset_Q_neg:
  assumes "rwf_query n V Q Qn"
  assumes "QQn \<subseteq> Qn"
  shows "rwf_query n V Q QQn"
proof -
  have "wf_query n V Q QQn"
  proof -
    have "\<forall>X\<in>QQn. wf_atable n X" by (meson Un_iff assms(1) assms(2) rwf_query_def subsetD wf_query_def)
    then show ?thesis
      by (meson UnE UnI1 assms(1) rwf_query_def wf_query_def)
  qed
  moreover have "included V QQn" by (meson assms(1) assms(2) included_def rwf_query_def subsetD)
  then show ?thesis by (metis (full_types) assms(2) non_empty_query_def subsetD assms(1) calculation rwf_query_def)
qed

lemma wf_secondRecursiveCalls:
  assumes "card V \<ge> 2"
  assumes "rwf_query n V Q Qn"
  assumes "(I, J) = getIJ Q Qn V"
  assumes "Qns \<subseteq> Qn"
  assumes "Q_J_neg = filterQuery J Qns"
  assumes "Q_J_pos = filterQuery J Q"
  shows "rwf_query n J (newQuery J Q_J_pos t) (newQuery J Q_J_neg t)"
proof -
  have "\<forall>X\<in>Q_J_pos. card (fst X \<inter> J) \<ge> 1"
    using set_filterQuery assms(2) assms(6) rwf_query_def by fastforce
  moreover have "card J \<ge> 1" by (metis assms(1) assms(3) getIJ.coreProperties getIJ_axioms)
  moreover have "wf_query n J Q_J_pos Qns"
  proof -
    have "wf_query n J Q Qns"
      by (metis subset_Q_neg wf_set_subset assms(1) assms(2) assms(3) assms(4)
          getIJ.coreProperties getIJ_axioms rwf_query_def sup_ge2 wf_query_def)
    moreover have "Q_J_pos \<subseteq> Q" using assms(6) by auto
    then have "\<forall>X\<in>(Q_J_pos \<union> Qns). wf_atable n X" using calculation wf_query_def by fastforce
    moreover have "card Q_J_pos \<ge> 1"
      by (metis wf_filterQuery(1) assms(1) assms(2) assms(3) assms(6) getIJ.coreProperties
          getIJ_axioms sup_ge2 wf_query_def)
    then show ?thesis using calculation(1) calculation(2) wf_query_def by blast
  qed
  moreover have "non_empty_query Q_J_pos"
    by (metis wf_filterQuery(2) assms(1) assms(2) assms(3) assms(6) getIJ.coreProperties
        getIJ_axioms sup_ge2)
  moreover have  "covering J Q_J_pos"
    by (metis wf_filterQuery(3) assms(1) assms(2) assms(3) assms(6) getIJ.coreProperties
        getIJ_axioms sup_ge2)
  moreover have "non_empty_query Q_J_neg"
    by (metis (no_types, lifting) filterQuery.elims assms(2) assms(4) assms(5) member_filter
        non_empty_query_def rwf_query_def subsetD)
  then show ?thesis
    using wf_newQuery assms(5) calculation(1) calculation(2) calculation(3) calculation(4)
      calculation(5) by blast
qed

lemma simple_merge_option:
  "merge_option (a, b) = None \<longleftrightarrow> (a = None \<and> b = None)"
  using merge_option.elims by blast

lemma wf_merge:
  assumes "wf_tuple n I t1"
  assumes "wf_tuple n J t2"
  assumes "V = I \<union> J"
  assumes "t = merge t1 t2"
  shows "wf_tuple n V t"
proof -
  have "\<And>i. i < n \<Longrightarrow> (t ! i = None \<longleftrightarrow> i \<notin> V)"
  proof -
    fix i
    assume "i < n"
    show "t ! i = None \<longleftrightarrow> i \<notin> V"
    proof (cases "t ! i = None")
      case True
      have "t = merge t1 t2" by (simp add: assms(4))
      then have "... = map merge_option (zip t1 t2)" by simp
      then have "merge_option (t1 ! i, t2 ! i) = None"
        by (metis True \<open>i < n\<close> assms(1) assms(2) assms(4) length_zip min_less_iff_conj nth_map nth_zip wf_tuple_def)
      obtain "t1 ! i = None" and "t2 ! i = None"
        by (meson \<open>merge_option (t1 ! i, t2 ! i) = None\<close> simple_merge_option)
      then show ?thesis
        using True \<open>i < n\<close> assms(1) assms(2) assms(3) wf_tuple_def by auto
    next
      case False
      have "t = map merge_option (zip t1 t2)" by (simp add: assms(4))
      then obtain x where "merge_option (t1 ! i, t2 ! i) = Some x"
        by (metis False \<open>i < n\<close> assms(1) assms(2) length_zip merge_option.elims min_less_iff_conj nth_map nth_zip wf_tuple_def)
      then show ?thesis
        by (metis False UnI1 UnI2 \<open>i < n\<close> assms(1) assms(2) assms(3) option.distinct(1) simple_merge_option wf_tuple_def)
    qed
  qed
  moreover have "length t = n"
  proof -
    obtain "length t1 = n" and "length t2 = n"
      using assms(1) assms(2) wf_tuple_def by blast
    then have "length (zip t1 t2) = n" by simp
    then show ?thesis by (simp add: assms(4))
  qed
  then show ?thesis by (simp add: calculation wf_tuple_def)
qed

lemma wf_inter:
  assumes "rwf_query n {i} Q Qn"
  assumes "(sa, a) \<in> Q"
  assumes "(sb, b) \<in> Q"
  shows "table n {i} (a \<inter> b)"
proof -
  obtain "card sa \<ge> 1" "card sb \<ge> 1"
    by (metis assms(1) assms(2) assms(3) fst_conv non_empty_query_def rwf_query_def)
  have "included {i} Q" using assms(1) rwf_query_def by blast
  then have "(\<forall>(S, X)\<in>Q. S \<subseteq> {i})" by (simp add: included_def)
  then obtain "sa \<subseteq> {i}" "sb \<subseteq> {i}" using assms(2) assms(3) by blast
  then obtain "sa = {i}" "sb = {i}"
    by (metis \<open>1 \<le> card sa\<close> \<open>1 \<le> card sb\<close> card_empty not_one_le_zero subset_singletonD)
  then show ?thesis
    using assms(1) assms(2) inf_le1 prod.sel(1) prod.sel(2) rwf_query_def wf_atable_def
      wf_atable_subset wf_query_def Un_iff by metis
qed

lemma table_subset:
  assumes "table n V T"
  assumes "S \<subseteq> T"
  shows "table n V S"
  using wf_atable_subset assms(1) assms(2) by blast

lemma wf_base_case:
  assumes "card V = 1"
  assumes "rwf_query n V Q Qn"
  assumes "R = genericJoin V Q Qn"
  shows "table n V R"
proof -
  have "wf_query n V Q Qn \<and> included V Q \<and> non_empty_query Q \<Longrightarrow> table n V ((\<Inter>(_, x) \<in> Q. x) - (\<Union>(_, x) \<in> Qn. x))"
  proof (induction "card Q - 1" arbitrary: Q)
    case 0
    have "card Q = 1"
      by (metis "0.hyps" "0.prems" One_nat_def le_add_diff_inverse plus_1_eq_Suc wf_query_def)
    obtain s x where "Q = {(s, x)}"
      by (metis One_nat_def \<open>card Q = 1\<close> card_eq_0_iff card_eq_SucD card_mono finite_insert insertE
          nat.simps(3) not_one_le_zero subrelI)
    moreover obtain i where "V = {i}" using assms(1) card_1_singletonE by auto
    then have "card s \<ge> 1"
    proof -
      have "(s, x) \<in> Q" by (simp add: calculation)
      moreover obtain X where "X = (s, x)" by simp
      then show ?thesis
        using "0.prems" calculation non_empty_query_def rwf_query_def by fastforce
    qed
    moreover obtain i where "V = {i}" using \<open>\<And>thesis. (\<And>i. V = {i} \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
    then have "s = {i}"
    proof -
      have "included {i} Q" using "0.prems" \<open>V = {i}\<close> rwf_query_def by simp
      then show ?thesis
        by (metis \<open>V = {i}\<close> assms(1) calculation(1) calculation(2) card_seteq case_prodD finite.emptyI finite.insertI included_def singletonI)
    qed
    moreover have "table n s x"
      using "0.prems" calculation(1) rwf_query_def wf_atable_def wf_query_def
      by (simp add: rwf_query_def wf_atable_def wf_query_def)
    then show ?case
      by (simp add: wf_atable_subset \<open>V = {i}\<close> calculation(1) calculation(3))
  next
    case (Suc y)
    obtain xx where "xx \<in> Q" by (metis Suc.hyps(2) all_not_in_conv card.empty nat.simps(3) zero_diff)
    moreover obtain H where "H = Q - {xx}" by simp
    then have "card H - 1 = y"
      by (metis Suc.hyps(2) calculation card_Diff_singleton card_infinite diff_Suc_1 less_imp_le not_one_le_zero zero_less_Suc zero_less_diff)
    moreover have "wf_query n V H Qn \<and> included V H \<and> non_empty_query H"
    proof -
      have "wf_query n V H Qn"
        using DiffD1 Suc.hyps(2) Suc.prems \<open>H = Q - {xx}\<close> calculation(1) card_Diff_singleton
          card_infinite le_add1 not_one_le_zero plus_1_eq_Suc wf_query_def
        by (metis (no_types, lifting) Un_iff)
      then show ?thesis
        using DiffD1 Suc.prems \<open>H = Q - {xx}\<close> included_def non_empty_query_def by fastforce
    qed
    then have "wf_query n V H Qn \<and> included V H \<and> non_empty_query H" by simp
    then have "table n V ((\<Inter>(_, x)\<in>H. x) - (\<Union>(_, x)\<in>Qn. x))" using Suc.hyps(1) calculation(2) by simp
    moreover obtain sa a where "(sa, a) \<in> H"
      by (metis One_nat_def Suc.hyps(2) \<open>H = Q - {xx}\<close> calculation(1) calculation(2) card_empty card_eq_0_iff card_le_Suc0_iff_eq diff_is_0_eq' equals0I insert_Diff le0 nat.simps(3) prod.collapse singletonD)
    moreover have "\<not> (Set.is_empty sa)"
      by (metis Set.is_empty_def \<open>wf_query n V H Qn \<and> included V H \<and> non_empty_query H\<close> calculation(4)
          card_empty non_empty_query_def not_one_le_zero prod.sel(1))
    then have "table n V (((\<Inter>(_, x) \<in> H. x) \<inter> (snd xx)) - (\<Union>(_, x)\<in>Qn. x))"
      by (metis Diff_Int2 Diff_Int_distrib2 IntE calculation(3) table_def)
    then show ?case using INF_insert Int_commute \<open>H = Q - {xx}\<close> calculation(1) insert_Diff snd_def by metis
  qed
  then show ?thesis
    using assms(1) assms(2) assms(3) genericJoin.simps le_numeral_extra(4) rwf_query_def by auto
qed

lemma filter_Q_J_neg_same:
  assumes "card V \<ge> 2"
  assumes "(I, J) = getIJ Q Qn V"
  assumes "Q_I_neg = filterQueryNeg I Qn"
  assumes "rwf_query n V Q Qn"
  shows "filterQuery J (Qn - Q_I_neg) = Qn - Q_I_neg" (is "?A = ?B")
proof-
  have "?A \<subseteq> ?B" by (simp add: subset_iff)
  moreover have "?B \<subseteq> ?A"
  proof (rule subsetI)
    fix x assume "x \<in> Qn - Q_I_neg"
    obtain A X where "(A, X) = x" by (metis surj_pair)
    have "card (A \<inter> J) \<ge> 1"
    proof (rule ccontr)
      assume "\<not> (card (A \<inter> J) \<ge> 1)"
      have "Set.is_empty (A \<inter> J)"
        by (metis One_nat_def Set.is_empty_def Suc_leI Suc_le_lessD \<open>\<not> 1 \<le> card (A \<inter> J)\<close> assms(1)
            assms(2) card_gt_0_iff finite_Int getIJ.coreProperties getIJ_axioms)
      moreover have "A \<subseteq> I"
      proof -
        have "(A, X) \<in> Qn" using \<open>(A, X) = x\<close> \<open>x \<in> Qn - Q_I_neg\<close> by auto
        then have "included V Qn" using assms(4) rwf_query_def by blast
        then have "A \<subseteq> V" using \<open>(A, X) \<in> Qn\<close> included_def by fastforce
        then show ?thesis
          by (metis Set.is_empty_def UnE assms(1) assms(2) calculation disjoint_iff_not_equal
              getIJProperties(5) subsetD subsetI)
      qed
      then have "(A, X) \<in> Q_I_neg" using \<open>(A, X) = x\<close> \<open>x \<in> Qn - Q_I_neg\<close> assms(3) by auto
      then show "False" using \<open>(A, X) = x\<close> \<open>x \<in> Qn - Q_I_neg\<close> by blast
    qed
    then show "x \<in> ?A" using \<open>(A, X) = x\<close> \<open>x \<in> Qn - Q_I_neg\<close>
      by (metis Diff_subset subset_Q_neg assms(4) fst_conv rwf_query_def set_filterQuery)
  qed
  then show ?thesis by auto
qed

lemma vars_genericJoin:
  assumes "card V \<ge> 2"
  assumes "(I, J) = getIJ Q Qn V"
  assumes "Q_I_pos = projectQuery I (filterQuery I Q)"
  assumes "Q_I_neg = filterQueryNeg I Qn"
  assumes "R_I = genericJoin I Q_I_pos Q_I_neg"
  assumes "Q_J_neg = filterQuery J (Qn - Q_I_neg)"
  assumes "Q_J_pos = filterQuery J Q"
  assumes "X = {(t, genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))) | t . t \<in> R_I}"
  assumes "R = (\<Union>(t, x) \<in> X. {merge xx t | xx . xx \<in> x})"
  assumes "rwf_query n V Q Qn"
  shows "R = genericJoin V Q Qn"
proof -
  have "filterQuery J (Qn - Q_I_neg) = Qn - Q_I_neg"
    using assms(1) assms(10) assms(2) assms(4) filter_Q_J_neg_same by blast
  then have "Q_J_neg = Qn - Q_I_neg" by (simp add: assms(6))
  moreover have "genericJoin V Q Qn =
    (if card V \<le> 1 then
      (\<Inter>(_, x) \<in> Q. x) - (\<Union>(_, x) \<in> Qn. x)
    else
      let (I, J) = getIJ Q Qn V in
      let Q_I_pos = projectQuery I (filterQuery I Q) in
      let Q_I_neg = filterQueryNeg I Qn in
      let R_I = genericJoin I Q_I_pos Q_I_neg in
      let Q_J_neg = Qn - Q_I_neg in
      let Q_J_pos = filterQuery J Q in
      let X = {(t, genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))) | t . t \<in> R_I} in
      (\<Union>(t, x) \<in> X. {merge xx t | xx . xx \<in> x}))"
    by simp
  moreover have "\<not> (card V \<le> 1)" using assms(1) by linarith
  then have gen: "genericJoin V Q Qn = (let (I, J) = getIJ Q Qn V in
      let Q_I_pos = projectQuery I (filterQuery I Q) in
      let Q_I_neg = filterQueryNeg I Qn in
      let R_I = genericJoin I Q_I_pos Q_I_neg in
      let Q_J_neg = Qn - Q_I_neg in
      let Q_J_pos = filterQuery J Q in
      let X = {(t, genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))) | t . t \<in> R_I} in
      (\<Union>(t, x) \<in> X. {merge xx t | xx . xx \<in> x}))"
    using assms by simp
  then have "... = (
      let Q_I_pos = projectQuery I (filterQuery I Q) in
      let Q_I_neg = filterQueryNeg I Qn in
      let R_I = genericJoin I Q_I_pos Q_I_neg in
      let Q_J_neg = Qn - Q_I_neg in
      let Q_J_pos = filterQuery J Q in
      let X = {(t, genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))) | t . t \<in> R_I} in
      (\<Union>(t, x) \<in> X. {merge xx t | xx . xx \<in> x}))"
    using assms(2) by (metis (no_types, lifting) case_prod_conv)
  then show ?thesis using assms by (metis calculation(1) gen)
qed

lemma base_genericJoin:
  assumes "card V \<le> 1"
  shows "genericJoin V Q Qn =  (\<Inter>(_, x) \<in> Q. x) - (\<Union>(_, x) \<in> Qn. x)"
proof -
  have "genericJoin V Q Qn =
    (if card V \<le> 1 then
      (\<Inter>(_, x) \<in> Q. x) - (\<Union>(_, x) \<in> Qn. x)
    else
      let (I, J) = getIJ Q Qn V in
      let Q_I_pos = projectQuery I (filterQuery I Q) in
      let Q_I_neg = filterQueryNeg I Qn in
      let R_I = genericJoin I Q_I_pos Q_I_neg in

      let Q_J_neg = Qn - Q_I_neg in
      let Q_J_pos = filterQuery J Q in
      let X = {(t, genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))) | t . t \<in> R_I} in
      (\<Union>(t, x) \<in> X. {merge xx t | xx . xx \<in> x}))"
    by simp
  then show ?thesis using assms by auto
qed

lemma wf_genericJoin:
  "\<lbrakk>rwf_query n V Q Qn; card V \<ge> 1\<rbrakk> \<Longrightarrow> table n V (genericJoin V Q Qn)"
proof (induction V Q Qn rule: genericJoin.induct)
  case (1 V Q Qn)
  then show ?case
  proof (cases "card V \<le> 1")
    case True
    then show ?thesis using "1.prems"(1) "1.prems"(2) le_antisym wf_base_case by blast
  next
    case False
    obtain I J where "(I, J) = getIJ Q Qn V" by (metis surj_pair)
    define Q_I_pos where "Q_I_pos = projectQuery I (filterQuery I Q)"
    define Q_I_neg where "Q_I_neg = filterQueryNeg I Qn"
    define R_I where "R_I = genericJoin I Q_I_pos Q_I_neg"
    define Q_J_neg where "Q_J_neg = filterQuery J (Qn - Q_I_neg)"
    define Q_J_pos where "Q_J_pos = filterQuery J Q"
    define X where "X = {(t, genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))) | t . t \<in> R_I}"
    define R where "R = (\<Union>(t, x) \<in> X. {merge xx t | xx . xx \<in> x})"
    moreover have "card V \<ge> 2" using False by auto
    then have "R = genericJoin V Q Qn"
      using vars_genericJoin[where ?V=V and ?I=I and ?J=J and ?Q_I_pos=Q_I_pos and ?Q=Q and ?Qn=Qn and
        ?Q_I_neg=Q_I_neg and ?R_I=R_I and ?Q_J_neg=Q_J_neg and ?Q_J_pos=Q_J_pos]
      using "1.prems"(1) Q_I_neg_def Q_I_pos_def Q_J_neg_def Q_J_pos_def R_I_def X_def \<open>(I, J) = getIJ Q Qn V\<close> calculation by blast
    obtain "card I \<ge> 1" "card J \<ge> 1"
      using \<open>(I, J) = getIJ Q Qn V\<close> \<open>2 \<le> card V\<close> getIJ.getIJProperties(1) getIJProperties(2) getIJ_axioms by blast
    moreover have "rwf_query n I Q_I_pos Q_I_neg"
      using "1.prems"(1) Q_I_neg_def Q_I_pos_def \<open>(I, J) = getIJ Q Qn V\<close> \<open>2 \<le> card V\<close> getIJ.wf_firstRecursiveCall getIJ_axioms by blast
    moreover have "\<And>t. t\<in>R_I \<Longrightarrow> table n J (genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t)))"
    proof -
      fix t assume "t \<in> R_I"
      have "rwf_query n J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))"
        using "1.prems"(1) Q_J_neg_def Q_J_pos_def \<open>(I, J) = getIJ Q Qn V\<close> \<open>2 \<le> card V\<close>
          getIJ.wf_secondRecursiveCalls getIJ_axioms by fastforce
      then show "table n J (genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t)))"
        by (metis "1.IH"(2) "1.prems"(1) False Q_I_neg_def Q_J_neg_def Q_J_pos_def \<open>(I, J) = getIJ Q Qn V\<close>
            \<open>2 \<le> card V\<close> calculation(3) filter_Q_J_neg_same)
    qed
    then have "\<And>t xx. t \<in> R_I \<and> xx \<in> (genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t)))
               \<Longrightarrow> wf_tuple n V (merge xx t)"
    proof -
      fix t xx assume "t \<in> R_I \<and> xx \<in> genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))"
      have "V = I \<union> J"
        using \<open>(I, J) = getIJ Q Qn V\<close> \<open>2 \<le> card V\<close> getIJ.coreProperties getIJ_axioms by metis
      moreover have "wf_tuple n J xx"
        using \<open>\<And>t. t \<in> R_I \<Longrightarrow> table n J (genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t)))\<close>
          \<open>t \<in> R_I \<and> xx \<in> genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))\<close> table_def by blast
      moreover have "wf_tuple n I t"
        by (metis "1.IH"(1) False Q_I_neg_def Q_I_pos_def
            R_I_def \<open>(I, J) = getIJ Q Qn V\<close> \<open>\<And>thesis. (\<lbrakk>1 \<le> card I; 1 \<le> card J\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
            \<open>rwf_query n I Q_I_pos Q_I_neg\<close> \<open>t \<in> R_I \<and> xx \<in> genericJoin J (newQuery J Q_J_pos (I, t))
            (newQuery J Q_J_neg (I, t))\<close> table_def)
      then show "wf_tuple n V (merge xx t)"
        by (metis calculation(1) calculation(2) sup_commute wf_merge)
    qed
    then have "\<forall>t\<in>R_I. \<forall>xx \<in> (genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))).
                wf_tuple n V (merge xx t)" by blast
    then have "\<forall>x\<in>R. wf_tuple n V x" using R_def X_def by blast
    then show ?thesis using \<open>R = genericJoin V Q Qn\<close> table_def by blast
  qed
qed

subsection \<open>Correctness\<close>

lemma base_correctness:
  assumes "card V = 1"
  assumes "rwf_query n V Q Qn"
  assumes "R = genericJoin V Q Qn"
  shows "z \<in> genericJoin V Q Qn \<longleftrightarrow> wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)"
proof -
  have "z \<in> genericJoin V Q Qn \<Longrightarrow> wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)"
  proof -
    fix z assume "z \<in> genericJoin V Q Qn"
    have "wf_tuple n V z" by (meson \<open>z \<in> genericJoin V Q Qn\<close> assms(1) assms(2) table_def wf_base_case)
    moreover have "\<And>A X. (A, X) \<in> Q \<Longrightarrow> restrict A z \<in> X"
    proof -
      fix A X assume "(A, X) \<in> Q"
      have "A = V"
      proof -
        have "card A \<ge> 1"
          using \<open>(A, X) \<in> Q\<close> assms(2) non_empty_query_def rwf_query_def by fastforce
        moreover have "A \<subseteq> V"
          using \<open>(A, X) \<in> Q\<close> assms(2) included_def rwf_query_def by fastforce
        then show ?thesis
          by (metis One_nat_def assms(1) calculation card_infinite card_seteq nat.simps(3))
      qed
      then have "restrict A z = z" using calculation restrict_idle by blast
      moreover have "z \<in> (\<Inter>(_, x) \<in> Q. x)"
        using \<open>z \<in> genericJoin V Q Qn\<close> assms(1) by auto
      then have "z \<in> X" using INT_D \<open>(A, X) \<in> Q\<close> case_prod_conv by auto
      then show "restrict A z \<in> X" using calculation by auto
    qed
    moreover have "\<And>A X. (A, X) \<in> Qn \<Longrightarrow> restrict A z \<notin> X"
    proof -
      fix A X assume "(A, X) \<in> Qn"
      have "card A \<ge> 1" using \<open>(A, X) \<in> Qn\<close> assms(2) non_empty_query_def rwf_query_def by fastforce
      moreover have "A \<subseteq> V" using \<open>(A, X) \<in> Qn\<close> assms(2) included_def rwf_query_def by blast
      then have "A = V" by (metis assms(1) calculation card_gt_0_iff card_seteq zero_less_one)
      then have "restrict A z = z"  using \<open>wf_tuple n V z\<close> restrict_idle by blast
      moreover have "z \<notin> (\<Union>(_, x) \<in> Qn. x)"
      proof -
        have "z \<in> (\<Inter>(_, x) \<in> Q. x) - (\<Union>(_, x) \<in> Qn. x)"
          using \<open>z \<in> genericJoin V Q Qn\<close> assms(1) by auto
        then show ?thesis by (metis DiffD2)
      qed
      then show "restrict A z \<notin> X" using UN_iff \<open>(A, X) \<in> Qn\<close> calculation(2) prod.sel(2) snd_def by auto
    qed
    then show "wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)"
      using calculation(1) calculation(2) by blast
  qed
  moreover have "wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X) \<Longrightarrow> z \<in> genericJoin V Q Qn"
  proof -
    assume "wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)"
    have "genericJoin V Q Qn = (\<Inter>(_, x) \<in> Q. x) - (\<Union>(_, x) \<in> Qn. x)" by (simp add: assms(1))
    moreover have "\<forall>(A, X)\<in>Q. restrict A z = z"
      by (metis (mono_tags, lifting) One_nat_def \<open>wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)\<close>
          assms(1) assms(2) card.infinite card_seteq case_prod_beta' included_def nat.simps(3)
          non_empty_query_def restrict_idle rwf_query_def)
    moreover have "card Q \<ge> 1" using assms(2) rwf_query_def wf_query_def by blast
    moreover have "z \<notin> (\<Union>(_, x) \<in> Qn. x)"
    proof -
      have "\<forall>(_, x) \<in> Qn. z \<notin> x"
        by (metis (mono_tags, lifting) One_nat_def \<open>wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)\<close>
            assms(1) assms(2) card.infinite card_seteq case_prod_beta' included_def nat.simps(3)
            non_empty_query_def restrict_idle rwf_query_def)
      then show ?thesis using UN_iff case_prod_beta' by auto
    qed
    moreover have "z \<in> (\<Inter>(_, x) \<in> Q. x)"
    proof -
      have "\<forall>(_, x) \<in> Q. z \<in> x"
        using \<open>wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)\<close> calculation(2) by fastforce
      then show ?thesis using INT_I case_prod_beta' by auto
    qed
    ultimately show ?thesis
    proof -
      have "genericJoin V Q Qn \<subseteq> R"
        using assms(3) by blast
      then have "(\<Inter>(N, Z)\<in>Q. Z) - (\<Union>(N, Z)\<in>Qn. Z) \<subseteq> R"
        by (metis \<open>genericJoin V Q Qn = (\<Inter>(_, x)\<in>Q. x) - (\<Union>(_, x)\<in>Qn. x)\<close>)
      then have "\<exists>Z Za. Z - Za \<subseteq> R \<and> z \<notin> Za \<and> z \<in> Z"
        by (metis \<open>z \<in> (\<Inter>(_, x)\<in>Q. x)\<close> \<open>z \<notin> (\<Union>(_, x)\<in>Qn. x)\<close>)
      then show ?thesis
        using assms(3) by blast
    qed
  qed
  then show ?thesis using calculation by linarith
qed

lemma simple_list_index_equality:
  assumes "length a = n"
  assumes "length b = n"
  assumes "\<forall>i < n. a!i = b!i"
  shows "a = b"
  using assms(1) assms(2) assms(3) nth_equalityI by force

lemma simple_restrict_none:
  assumes "i < length X"
  assumes "i \<notin> A"
  shows "(restrict A X)!i = None"
  by (simp add: assms(1) assms(2) restrict_def)

lemma simple_restrict_some:
  assumes "i < length X"
  assumes "i \<in> A"
  shows "(restrict A X)!i = X!i"
  by (simp add: assms(1) assms(2) restrict_def)

lemma merge_restrict:
  assumes "A \<inter> J = {}"
  assumes "A \<subseteq> I"
  assumes "length xx = n"
  assumes "length t = n"
  assumes "restrict J xx = xx"
  shows "restrict A (merge xx t) = restrict A t"
proof -
  have "\<And>i. i < n \<Longrightarrow> (restrict A (merge xx t))!i = (restrict A t)!i"
  proof -
    fix i assume "i < n"
    show "(restrict A (merge xx t))!i = (restrict A t)!i"
    proof (cases "i \<in> A")
      case True
      have "(restrict A t)!i = t!i" by (simp add: True \<open>i < n\<close> assms(4) nth_restrict)
      moreover have "(restrict A (merge xx t))!i = t!i"
      proof -
        have "xx!i = None"
          by (metis True \<open>i < n\<close> assms(1) assms(3) assms(5) disjoint_iff_not_equal simple_restrict_none)
        obtain "length xx = length t" by (simp add: assms(3) assms(4))
        moreover have "(merge xx t)!i = merge_option (xx!i, t!i)"
          using \<open>i < n\<close> \<open>length xx = length t\<close> assms(3) by auto
        moreover have "merge_option (None, t!i) = t!i" 
          by (metis merge_option.simps(1) merge_option.simps(3) option.exhaust)
        then have "(merge xx t)!i = t!i" using \<open>xx ! i = None\<close> calculation(2) by auto
        moreover have "(restrict A (merge xx t))!i = (merge xx t)!i"
        proof -
          have "length (zip xx t) = n" using assms(3) calculation(1) by auto
          then have "length (merge xx t) = n" by simp
          then show ?thesis by (simp add: True \<open>i < n\<close> nth_restrict)
        qed
        then show ?thesis using calculation(3) by auto
      qed
      then show ?thesis by (simp add: calculation)
    next
      case False
      have "(restrict A t)!i = None" by (simp add: False \<open>i < n\<close> assms(4) restrict_def)
      obtain "length xx = n" and "length t = n"
        by (simp add: assms(3) assms(4))
      then have "length (merge xx t) = n" by simp
      moreover have "(restrict A (merge xx t))!i = None"
        using False \<open>i < n\<close> calculation simple_restrict_none by blast
      then show ?thesis by (simp add: \<open>restrict A t ! i = None\<close>)
    qed
  qed
  then have "\<forall>i < n. (restrict A (merge xx t))!i = (restrict A t)!i" by blast
  then show ?thesis using simple_list_index_equality[where ?a="restrict A (merge xx t)" and ?b="restrict A t" and ?n="n"]
      assms(3) assms(4) by simp
qed

lemma restrict_idle_include:
  assumes "wf_tuple n A v"
  assumes "A \<subseteq> I"
  shows "restrict I v = v"
proof -
  have "\<And>i. i < length v \<Longrightarrow> (restrict I v)!i = v!i"
  proof -
    fix i assume "i < length v"
    show "(restrict I v)!i = v!i"
    proof (cases "i \<in> A")
      case True
      then show ?thesis using \<open>i < length v\<close> assms(2) nth_restrict by blast
    next
      case False
      then show ?thesis by (metis \<open>i < length v\<close> assms(1) nth_restrict simple_restrict_none wf_tuple_def)
    qed
  qed
  then show ?thesis by (simp add: list_eq_iff_nth_eq)
qed

lemma merge_index:
  assumes "I \<inter> J = {}"
  assumes "wf_tuple n I tI"
  assumes "wf_tuple n J tJ"
  assumes "t = merge tI tJ"
  assumes "i < n"
  shows "(i \<in> I \<and> t!i = tI!i) \<or> (i \<in> J \<and> t!i = tJ!i) \<or> (i \<notin> I \<and> i \<notin> J \<and> t!i = None)"
proof -
  have "t!i = merge_option ((zip tI tJ)!i)"
    by (metis (full_types) assms(2) assms(3) assms(4) assms(5) length_zip merge.simps
        min_less_iff_conj nth_map wf_tuple_def)
  then have "t!i = merge_option (tI!i, tJ!i)" by (metis assms(2) assms(3) assms(5) nth_zip wf_tuple_def)
  then show ?thesis
  proof (cases "i \<in> I")
    case True
    have "t!i = tI!i"
    proof -
      have "tJ!i = None" by (meson True assms(1) assms(3) assms(5) disjoint_iff_not_equal wf_tuple_def)
      moreover have "merge_option (tI!i, None) = tI!i"
        by (metis True assms(2) assms(5) merge_option.simps(2) option.exhaust wf_tuple_def)
      then show ?thesis by (simp add: \<open>t ! i = merge_option (tI ! i, tJ ! i)\<close> calculation)
    qed
    then show ?thesis using True by blast
  next
    case False
    have "i \<notin> I" by (simp add: False)
    then show ?thesis
    proof (cases "i \<in> J")
      case True
      have "t!i = tJ!i"
      proof -
        have "tI!i = None" using False assms(2) assms(5) wf_tuple_def by blast
        moreover have "merge_option (None, tJ!i) = tJ!i"
          by (metis True assms(3) assms(5) merge_option.simps(3) option.exhaust wf_tuple_def)
        then show ?thesis by (simp add: \<open>t ! i = merge_option (tI ! i, tJ ! i)\<close> calculation)
      qed
      then show ?thesis using True by blast
    next
      case False
      obtain "tI!i = None" and "tJ!i = None " by (meson False \<open>i \<notin> I\<close> assms(2) assms(3) assms(5) wf_tuple_def)
      have "t!i = None"
        by (simp add: \<open>t ! i = merge_option (tI ! i, tJ ! i)\<close> \<open>tI ! i = None\<close> \<open>tJ ! i = None\<close>)
      then show ?thesis using False \<open>i \<notin> I\<close> by blast
    qed
  qed
qed

lemma restrict_index_in:
  assumes "i < length X"
  assumes "i \<in> I"
  shows "(restrict I X)!i = X!i"
  by (simp add: assms(1) assms(2) nth_restrict)

lemma restrict_index_out:
  assumes "i < length X"
  assumes "i \<notin> I"
  shows "(restrict I X)!i = None"
  by (simp add: assms(1) assms(2) simple_restrict_none)

lemma merge_length:
  assumes "length a = n"
  assumes "length b = n"
  shows "length (merge a b) = n"
  by (simp add: assms(1) assms(2))

lemma real_restrict_merge:
  assumes "I \<inter> J = {}"
  assumes "wf_tuple n I tI"
  assumes "wf_tuple n J tJ"
  shows "restrict I (merge tI tJ) = restrict I tI \<and> restrict J (merge tI tJ) = restrict J tJ"
proof -
  have "length (merge tI tJ) = n"
    using assms(2) assms(3) merge_length wf_tuple_def by blast
  have "\<And>i. i < n \<Longrightarrow> (restrict I (merge tI tJ))!i = (restrict I tI)!i
                     \<and> (restrict J (merge tI tJ))!i = (restrict J tJ)!i"
  proof -
    fix i assume "i < n"
    show "(restrict I (merge tI tJ))!i = (restrict I tI)!i \<and> (restrict J (merge tI tJ))!i = (restrict J tJ)!i"
    proof (cases "i \<in> I")
      case True
      have "(merge tI tJ)!i = tI!i"
        by (meson True \<open>i < n\<close> assms(1) assms(2) assms(3) disjoint_iff_not_equal merge_index)
      then have "(restrict I (merge tI tJ))!i = tI!i"
        by (metis True \<open>i < n\<close> \<open>length (merge tI tJ) = n\<close> simple_restrict_some)
      then show ?thesis
        by (metis True \<open>i < n\<close> \<open>length (merge tI tJ) = n\<close> assms(1) assms(2) assms(3) disjoint_iff_not_equal restrict_idle simple_restrict_none wf_tuple_def)
    next
      case False
      have "i \<notin> I" by (simp add: False)
      then show ?thesis
      proof (cases "i \<in> J")
        case True
        have "(merge tI tJ)!i = tJ!i"
          using True \<open>i < n\<close> assms(1) assms(2) assms(3) merge_index by blast
        then show ?thesis
          by (metis (no_types, lifting) False \<open>i < n\<close> \<open>length (merge tI tJ) = n\<close> assms(2) assms(3) simple_restrict_none simple_restrict_some wf_tuple_def)
      next
        case False
        have "(merge tI tJ)!i = None" using False \<open>i < n\<close> \<open>i \<notin> I\<close> assms(1) assms(2) assms(3) merge_index by blast
        then show ?thesis 
          by (metis False \<open>i < n\<close> \<open>i \<notin> I\<close> \<open>length (merge tI tJ) = n\<close> assms(2) assms(3) eq_iff equalityD1 restrict_idle_include simple_restrict_none wf_tuple_def wf_tuple_restrict_simple)
      qed
    qed
  qed
  then obtain "\<forall>i < n. (restrict I (merge tI tJ))!i = (restrict I tI)!i" 
          and "\<forall>i < n. (restrict J (merge tI tJ))!i = (restrict J tJ)!i" by blast
  moreover have "length (merge tI tJ) = n" by (meson assms(2) assms(3) wf_merge wf_tuple_def)
  moreover obtain "length (restrict I tI) = n" and "length (restrict J tJ) = n"
    using assms(2) assms(3) wf_tuple_def by auto
  then show ?thesis
    by (metis \<open>\<And>i. i < n \<Longrightarrow> restrict I (merge tI tJ) ! i = restrict I tI ! i \<and> restrict J (merge tI tJ) ! i = restrict J tJ ! i\<close> calculation(3) length_restrict simple_list_index_equality)
qed

lemma simple_set_image_id:
  assumes "\<forall>x\<in>X. f x = x"
  shows "Set.image f X = X"
proof -
  have "Set.image f X = {f x |x. x \<in> X}" by (simp add: Setcompr_eq_image)
  then have "... = {x |x. x \<in> X}" by (simp add: assms)
  moreover have "... = X" by simp
  then show ?thesis by (simp add: \<open>f ` X = {f x |x. x \<in> X}\<close> calculation)
qed

lemma nested_include_restrict:
  assumes "restrict I z = t"
  assumes "A \<subseteq> I"
  shows "restrict A z = restrict A t"
proof -
  have "length (restrict A z) = length (restrict A t)" using assms(1) by auto
  moreover have "\<And>i. i < length (restrict A z) \<Longrightarrow> (restrict A z) ! i = (restrict A t) ! i"
  proof -
    fix i assume "i < length (restrict A z)"
    then show "(restrict A z) ! i = (restrict A t) ! i"
    proof (cases "i \<in> A")
      case True
      then show ?thesis
        by (metis restrict_index_in \<open>i < length (restrict A z)\<close> assms(1) assms(2) length_restrict subsetD)
    next
      case False
      then show ?thesis
        by (metis simple_restrict_none \<open>i < length (restrict A z)\<close> calculation length_restrict)
    qed
  qed
  ultimately show ?thesis by (simp add: list_eq_iff_nth_eq)
qed

lemma restrict_nested:
  "restrict A (restrict B x) = restrict (A \<inter> B) x" (is "?lhs = ?rhs")
proof -
  have "\<And>i. i < length x \<Longrightarrow> ?lhs!i = ?rhs!i"
    by (metis Int_iff length_restrict restrict_index_in simple_restrict_none)
  then show ?thesis by (simp add: simple_list_index_equality)
qed

lemma newQuery_equi_dev:
  "newQuery V Q (I, t) = Set.image (projectTable V) (Set.image (\<lambda>tab. semiJoin tab (I, t)) Q)"
  by (metis newQuery_equiv_def projectQuery.elims)

lemma projectTable_idle:
  assumes "table n A X"
  assumes "A \<subseteq> I"
  shows "projectTable I (A, X) = (A, X)"
proof -
  have "projectTable I (A, X) = (A \<inter> I, Set.image (restrict I) X)"
          using projectTable.simps by blast
  then have "A \<inter> I = A" using assms(2) by blast
  have "\<And>x. x \<in> X \<Longrightarrow> (restrict I) x = x"
  proof -
    fix x assume "x \<in> X"
    have "wf_tuple n A x" using \<open>x \<in> X\<close> assms(1) table_def by blast
    then show "(restrict I) x = x" using assms(2) restrict_idle_include by blast
  qed
  then have "\<forall>x \<in> X. (restrict I) x = x" by blast
  moreover have "Set.image (restrict I) X = X"
    by (simp add: \<open>\<And>x. x \<in> X \<Longrightarrow> restrict I x = x\<close>)
  then show ?thesis by (simp add: \<open>A \<inter> I = A\<close>)
qed

lemma restrict_partition_merge:
  assumes "I \<union> J = V"
  assumes "wf_tuple n V z"
  assumes "xx = restrict J z"
  assumes "t = restrict I z"
  assumes "Set.is_empty (I \<inter> J)"
  shows "z = merge xx t"
proof -
  have "\<And>i. i < n \<Longrightarrow> z!i = (merge xx t)!i"
  proof -
    fix i assume "i < n"
    show "z!i = (merge xx t)!i"
    proof (cases "i \<in> I")
      case True
      have "z!i = t!i"
        by (metis True \<open>i < n\<close> assms(2) assms(4) nth_restrict wf_tuple_def)
      moreover have "(merge xx t)!i = t!i"
      proof -
        have "xx ! i = None"
          by (metis simple_restrict_none Set.is_empty_def True \<open>i < n\<close> assms(2) assms(3) assms(5) disjoint_iff_not_equal wf_tuple_length)
        moreover have "(merge xx t) ! i = merge_option (xx ! i, t ! i)" using \<open>i < n\<close> assms(2) assms(3) assms(4) wf_tuple_length by fastforce
        ultimately show ?thesis
        proof (cases "t ! i")
          case None
          then show ?thesis using \<open>merge xx t ! i = merge_option (xx ! i, t ! i)\<close> \<open>xx ! i = None\<close> by auto
        next
          case (Some a)
          then show ?thesis using \<open>merge xx t ! i = merge_option (xx ! i, t ! i)\<close> \<open>xx ! i = None\<close> by auto
        qed
      qed
      then show ?thesis by (simp add: calculation)
    next
      case False
      have "i \<notin> I" by (simp add: False)
      then show ?thesis
      proof (cases "i \<in> J")
        case True
        have "z!i = xx!i"
          by (metis True \<open>i < n\<close> assms(2) assms(3) nth_restrict wf_tuple_def)
        moreover have "(merge xx t)!i = xx!i"
        proof (cases "xx ! i")
          case None
          then show ?thesis  by (metis True UnI1 \<open>i < n\<close> assms(1) assms(2) calculation sup_commute wf_tuple_def)
        next
          case (Some a)
          have "t ! i = None" by (metis False simple_restrict_none \<open>i < n\<close> assms(2) assms(4) wf_tuple_length)
          then show ?thesis using Some \<open>i < n\<close> assms(2) assms(3) assms(4) wf_tuple_length by fastforce
        qed
        then show ?thesis by (simp add: calculation)
      next
        case False
        have "z!i = None" by (metis False UnE \<open>i < n\<close> \<open>i \<notin> I\<close> assms(1) assms(2) wf_tuple_def)
        moreover have "(merge xx t)!i = None"
        proof -
          have "xx ! i = None"
            by (metis False New_max.simple_restrict_none \<open>i < n\<close> assms(2) assms(3) wf_tuple_length)
          moreover have "t ! i = None"
            by (metis New_max.simple_restrict_none \<open>i < n\<close> \<open>i \<notin> I\<close> assms(2) assms(4) wf_tuple_length)
          ultimately show ?thesis using \<open>i < n\<close> assms(2) assms(3) assms(4) wf_tuple_length by fastforce
        qed
        then show ?thesis by (simp add: calculation)
      qed
    qed
  qed
  moreover have "length z = n" using assms(2) wf_tuple_def by blast
  then show ?thesis
    by (simp add: assms(3) assms(4) calculation simple_list_index_equality)
qed

lemma restrict_merge:
  assumes "zI = restrict I z"
  assumes "zJ = restrict J z"
  assumes "restrict (A \<inter> I) zI \<in> Set.image (restrict I) X"
  assumes "restrict (A \<inter> J) zJ \<in> Set.image (restrict J) (Set.filter (isSameIntersection zI (A \<inter> I)) X)"
  assumes "z = merge zJ zI"
  assumes "table n A X"
  assumes "A \<subseteq> I \<union> J"
  assumes "card (A \<inter> I) \<ge> 1"
  assumes "wf_set n (I \<union> J)"
  assumes "wf_tuple n (I \<union> J) z"
  shows "restrict A z \<in> X"
proof -
  define zAJ where "zAJ = restrict (A \<inter> J) zJ"
  obtain zz where "zAJ = restrict J zz" "isSameIntersection zI (A \<inter> I) zz" "zz \<in> X"
    using assms(4) zAJ_def by auto
  then have "restrict (A \<inter> I) zz = restrict A zI"
  proof -
    have "restrict (A \<inter> I) zI = restrict (A \<inter> I) zz"
    proof -
      have "wf_set n A" using assms(7) assms(9) wf_set_def by auto
      moreover have "wf_tuple n I zI" using assms(1) assms(10) wf_tuple_restrict_simple by auto
      moreover have "wf_tuple n A zz" using \<open>zz \<in> X\<close> assms(6) table_def by blast
      moreover obtain "A \<inter> I \<subseteq> A" "A \<inter> I \<subseteq> I" by simp
      then show ?thesis using isSame_equi_dev[of n _ I zI A zz "A \<inter> I"]
        using \<open>isSameIntersection zI (A \<inter> I) zz\<close> assms(7) assms(9) calculation(2) calculation(3) by blast
    qed
    then show ?thesis
      by (simp add: restrict_nested assms(1))
  qed
  then have "zz = restrict A z"
  proof -
    have "length zz = n" using \<open>zz \<in> X\<close> assms(6) table_def wf_tuple_def by blast
    moreover have "length (restrict A z) = n"
      by (metis \<open>restrict (A \<inter> I) zz = restrict A zI\<close> assms(1) calculation length_restrict)
    moreover have "\<And>i. i < n \<Longrightarrow> zz!i = (restrict A z)!i"
    proof -
      fix i assume "i < n"
      show "zz!i = (restrict A z)!i"
      proof (cases "i \<in> A")
        case True
        have "i \<in> A" using True by simp
        then show ?thesis
        proof (cases "i \<in> I")
          case True
          have "zz!i = (restrict (A \<inter> I) zz)!i"
            by (simp add: True \<open>i < n\<close> \<open>i \<in> A\<close> calculation(1) restrict_index_in)
          then have "... = (restrict A zI)!i" by (simp add: \<open>restrict (A \<inter> I) zz = restrict A zI\<close>)
          then show ?thesis
            by (metis True \<open>i < n\<close> \<open>i \<in> A\<close> \<open>zz ! i = restrict (A \<inter> I) zz ! i\<close> assms(1) calculation(2)
                length_restrict restrict_index_in)
        next
          case False
          have "zz!i = (restrict (A \<inter> J) zJ)!i"
            by (metis False True UnE \<open>i < n\<close> \<open>zAJ = restrict J zz\<close> assms(7) calculation(1)
                restrict_index_in subsetD zAJ_def)
          then have "... = (restrict A zJ)!i" by (simp add: assms(2) restrict_nested)
          then show ?thesis
            by (metis False True UnE \<open>i < n\<close> \<open>zz ! i = restrict (A \<inter> J) zJ ! i\<close> assms(2) assms(7)
                calculation(2) length_restrict restrict_index_in subsetD)
        qed
      next
        case False
        then show ?thesis
          by (metis \<open>i < n\<close> \<open>zz \<in> X\<close> assms(6) calculation(2) length_restrict simple_restrict_none table_def wf_tuple_def)
      qed
    qed
    then show ?thesis using calculation(1) calculation(2) simple_list_index_equality by blast
  qed
  then show ?thesis
    using \<open>zz \<in> X\<close> by auto
qed

lemma partial_correctness:
  assumes "V = I \<union> J"
  assumes "Set.is_empty (I \<inter> J)"
  assumes "card I \<ge> 1"
  assumes "card J \<ge> 1"
  assumes "Q_I_pos = projectQuery I (filterQuery I Q)"
  assumes "Q_J_pos = filterQuery J Q"
  assumes "Q_I_neg = filterQueryNeg I Qn"
  assumes "Q_J_neg = filterQuery J (Qn - Q_I_neg)"
  assumes "NQ_pos = newQuery J Q_J_pos (I, t)"
  assumes "NQ_neg = newQuery J Q_J_neg (I, t)"
  assumes "R_NQ = genericJoin J NQ_pos NQ_neg"
  assumes "\<forall>x. (x \<in> R_I \<longleftrightarrow> wf_tuple n I x \<and> (\<forall>(A, X)\<in>Q_I_pos. restrict A x \<in> X) \<and> (\<forall>(A, X)\<in>Q_I_neg. restrict A x \<notin> X))"
  assumes "\<forall>y. (y \<in> R_NQ \<longleftrightarrow> wf_tuple n J y \<and> (\<forall>(A, X)\<in>NQ_pos. restrict A y \<in> X) \<and> (\<forall>(A, X)\<in>NQ_neg. restrict A y \<notin> X))"
  assumes "z = merge xx t"
  assumes "t \<in> R_I"
  assumes "xx \<in> R_NQ"
  assumes "rwf_query n V Q Qn"
  shows "wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)"
proof -
  obtain "wf_tuple n I t" "wf_tuple n J xx"
    using assms(12) assms(13) assms(15) assms(16) by blast
  then have "wf_tuple n V z"
    by (metis wf_merge assms(1) assms(14) sup_commute)
  moreover have "\<And>A X. (A, X) \<in> Qn \<Longrightarrow> restrict A z \<notin> X"
  proof -
    fix A X assume "(A, X) \<in> Qn"
    have "restrict I (merge xx t) = restrict I t"
      by (metis (no_types, lifting) Set.is_empty_def \<open>\<And>thesis. (\<lbrakk>wf_tuple n I t; wf_tuple n J xx\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
          assms(2) merge_restrict restrict_idle sup.cobounded1 wf_tuple_def)
    moreover have "restrict J (merge xx t) = restrict J xx"
      by (metis Set.is_empty_def \<open>\<And>thesis. (\<lbrakk>wf_tuple n I t; wf_tuple n J xx\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
          assms(2) inf_commute real_restrict_merge)
    moreover have "restrict J xx = xx" using \<open>wf_tuple n J xx\<close> restrict_idle by auto
    moreover have "restrict I t = t" using \<open>wf_tuple n I t\<close> restrict_idle by auto
    then obtain "restrict I z = t" "restrict J z = xx"
      using assms(14) calculation(1) calculation(2) calculation(3) by auto
    moreover have "\<forall>(A, X)\<in>Q_I_pos. restrict A t \<in> X" using assms(12) assms(15) by blast
    moreover have "\<forall>(A, X)\<in>NQ_pos. restrict A xx \<in> X" using assms(13) assms(16) by blast
    moreover have "card A \<ge> 1"
      using \<open>(A, X) \<in> Qn\<close> assms(17) non_empty_query_def rwf_query_def by fastforce
    then show "restrict A z \<notin> X"
    proof (cases "A \<subseteq> I")
      case True
      have "(A, X) \<in> Q_I_neg" by (simp add: True \<open>(A, X) \<in> Qn\<close> assms(7))
      have "table n A X"
      proof -
        have "wf_query n V Q Qn" using assms(17) rwf_query_def by blast
        moreover have "(A, X) \<in> (Q \<union> Qn)" by (simp add: \<open>(A, X) \<in> Qn\<close>)
        then show ?thesis by (metis calculation fst_conv snd_conv wf_atable_def wf_query_def)
      qed
      then have "restrict A t \<notin> X" using \<open>(A, X) \<in> Q_I_neg\<close> assms(12) assms(15) by blast
      moreover have "restrict A z = restrict A t" using True \<open>restrict I z = t\<close> nested_include_restrict by blast
      then show ?thesis by (simp add: calculation)
    next
      case False
      have "(A, X) \<in> Q_J_neg"
      proof -
        have "(A, X) \<in> Qn - Q_I_neg" using False \<open>(A, X) \<in> Qn\<close> assms(7) by auto
        moreover have "card (A \<inter> J) \<ge> 1"
          by (metis (no_types, lifting) False Int_greatest One_nat_def Set.is_empty_def Suc_leI
              Suc_le_lessD \<open>(A, X) \<in> Qn\<close> assms(1) assms(17) assms(2) assms(4) card_gt_0_iff case_prodD
              finite_Int included_def rwf_query_def sup_ge2 sup_inf_absorb sup_inf_distrib1)
        then show ?thesis using assms(8) calculation
          by (metis Diff_subset subset_Q_neg assms(17) fst_conv rwf_query_def set_filterQuery)
      qed
      define AI where "AI = A \<inter> I"
      define AJ where "AJ = A \<inter> J"
      then have "NQ_neg = projectQuery J (Set.image (\<lambda>tab. semiJoin tab (I, t)) Q_J_neg)"
        by (metis newQuery_equi_dev projectQuery.simps assms(10))
      then obtain XX where "(A, XX) = (\<lambda>tab. semiJoin tab (I, t)) (A, X)" by simp
      then obtain XXX where "(AJ, XXX) \<in> NQ_neg" and "(AJ, XXX) = projectTable J (A, XX)"
        by (metis AJ_def newQuery.simps projectTable.simps \<open>(A, X) \<in> Q_J_neg\<close> assms(10) image_eqI)
      then have "restrict AJ xx \<notin> XXX"
      proof -
        have "xx \<in> R_NQ" by (simp add: assms(16))
        then have "wf_tuple n J xx \<and> (\<forall>(A, X)\<in>NQ_pos. restrict A xx \<in> X) \<and> (\<forall>(A, X)\<in>NQ_neg. restrict A xx \<notin> X)"
          by (simp add: assms(13))
        then show ?thesis using \<open>(AJ, XXX) \<in> NQ_neg\<close> by blast
      qed

      define zA where "zA = restrict A z"
      have "zA \<notin> X"
      proof (rule ccontr)
        assume "\<not> (zA \<notin> X)"
        then have "zA \<in> X" by simp
        moreover have "restrict (A \<inter> I) zA = restrict (A \<inter> I) t"
          by (metis nested_include_restrict \<open>restrict I z = t\<close> inf_le1 inf_le2 zA_def)
        then have "isSameIntersection t (A \<inter> I) zA"
        proof -
          have "wf_set n V" using assms(17) rwf_query_def wf_query_def by blast
          moreover obtain "A \<inter> I \<subseteq> A" "A \<inter> I \<subseteq> I" "I \<subseteq> V" using assms(1) by blast
          moreover have "A \<subseteq> V" using \<open>(A, X) \<in> Qn\<close> assms(17) included_def rwf_query_def by fastforce
          moreover have "wf_tuple n A zA"
            using \<open>wf_tuple n V z\<close> calculation(5) wf_tuple_restrict_simple zA_def by blast
          then show ?thesis using isSame_equi_dev[of n V A zA I t "A \<inter> I"]
            by (simp add: \<open>restrict (A \<inter> I) zA = restrict (A \<inter> I) t\<close> \<open>wf_tuple n I t\<close> calculation(1) calculation(4) calculation(5))
        qed
        then have "zA \<in> XX" using \<open>(A, XX) = semiJoin (A, X) (I, t)\<close> calculation by auto
        then have "restrict J zA \<in> XXX" using \<open>(AJ, XXX) = projectTable J (A, XX)\<close> by auto
        moreover have "restrict AJ xx = restrict J zA"
          by (metis AJ_def restrict_nested \<open>restrict J z = xx\<close> inf.right_idem inf_commute zA_def)
        then show "False" using \<open>restrict AJ xx \<notin> XXX\<close> calculation(2) by auto
      qed
      then show ?thesis using zA_def by auto
    qed
  qed
  moreover have "\<And>A X. (A, X) \<in> Q \<Longrightarrow> restrict A z \<in> X"
  proof -
    fix A X assume "(A, X) \<in> Q"
    have "restrict I (merge xx t) = restrict I t"
      by (metis (no_types, lifting) Set.is_empty_def \<open>\<And>thesis. (\<lbrakk>wf_tuple n I t; wf_tuple n J xx\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
          assms(2) merge_restrict restrict_idle sup.cobounded1 wf_tuple_def)
    moreover have "restrict J (merge xx t) = restrict J xx"
      by (metis Set.is_empty_def \<open>\<And>thesis. (\<lbrakk>wf_tuple n I t; wf_tuple n J xx\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
          assms(2) inf_commute real_restrict_merge)
    moreover have "restrict J xx = xx" using \<open>wf_tuple n J xx\<close> restrict_idle by auto
    moreover have "restrict I t = t" using \<open>wf_tuple n I t\<close> restrict_idle by auto
    then obtain "restrict I z = t" "restrict J z = xx"
      using assms(14) calculation(1) calculation(2) calculation(3) by auto
    moreover have "\<forall>(A, X)\<in>Q_I_pos. restrict A t \<in> X" using assms(12) assms(15) by blast
    moreover have "\<forall>(A, X)\<in>NQ_pos. restrict A xx \<in> X" using assms(13) assms(16) by blast
    moreover have "card A \<ge> 1"
      using \<open>(A, X) \<in> Q\<close> assms(17) non_empty_query_def rwf_query_def by fastforce
    then show "restrict A z \<in> X"
    proof (cases "A \<subseteq> I")
      case True
      have "(A, X) \<in> filterQuery I Q"
      proof -
        have "A \<inter> I = A" using True by auto
        then have "A \<inter> I \<noteq> {}" using \<open>1 \<le> card A\<close> by auto
        then have "(\<lambda>(s, _). s \<inter> V \<noteq> {}) (A, X)" using assms(1) by blast
        then show ?thesis
          by (metis \<open>(A, X) \<in> Q\<close> \<open>1 \<le> card A\<close> \<open>A \<inter> I = A\<close> assms(17) fst_conv rwf_query_def set_filterQuery)          
      qed
      have "table n A X"
      proof -
        have "wf_query n V Q Qn" using assms(17) rwf_query_def by blast
        moreover have "(A, X) \<in> (Q \<union> Qn)" by (simp add: \<open>(A, X) \<in> Q\<close>)
        then show ?thesis by (metis calculation fst_conv snd_conv wf_atable_def wf_query_def)
      qed
      moreover have "projectTable I (A, X) = (A, X)" using True calculation projectTable_idle by blast
      then have "(A, X) \<in> Q_I_pos" by (metis \<open>(A, X) \<in> filterQuery I Q\<close> assms(5) image_eqI projectQuery.elims)
      then have "restrict A t \<in> X" using \<open>\<forall>(A, X)\<in>Q_I_pos. restrict A t \<in> X\<close> by blast
      moreover have "restrict A z = restrict A t" using True \<open>restrict I z = t\<close> nested_include_restrict by blast
      then show ?thesis by (simp add: calculation(2))
    next
      case False
      have "A \<subseteq> V"
      proof -
        have "included V Q" using assms(17) rwf_query_def by blast
        then show ?thesis using \<open>(A, X) \<in> Q\<close> included_def by fastforce
      qed
      then have "card (A \<inter> J) \<ge> 1" by (metis False One_nat_def Suc_leI Suc_le_lessD UnE assms(1) 
            assms(4) card_gt_0_iff disjoint_iff_not_equal finite_Int subsetD subsetI)
      then show ?thesis
      proof (cases "card (A \<inter> I) \<ge> 1")
        case True
        define zI where "zI = restrict I z"
        define zJ where "zJ = restrict J z"
        obtain "zI = t" "zJ = xx"
          by (simp add: calculation(4) calculation(5) zI_def zJ_def)
        then have "wf_tuple n I zI \<and> (\<forall>(A, X)\<in>Q_I_pos. restrict A zI \<in> X)"
          using \<open>wf_tuple n I t\<close> calculation(6) by blast
        moreover have "wf_tuple n J zJ \<and> (\<forall>(A, X)\<in>NQ_pos. restrict A zJ \<in> X)"
          using \<open>\<forall>(A, X)\<in>NQ_pos. restrict A xx \<in> X\<close> \<open>wf_tuple n J xx\<close> \<open>zJ = xx\<close> by blast
        obtain "(A, X) \<in> (filterQuery I Q)" "(A, X) \<in> Q_J_pos"
          using True \<open>(A, X) \<in> Q\<close> \<open>1 \<le> card (A \<inter> J)\<close> assms(6) assms(17) rwf_query_def set_filterQuery by fastforce
        define AI where "AI = A\<inter>I"
        define XI where "XI = Set.image (restrict I) X"
        then have "(AI, XI) = projectTable I (A, X)" using AI_def XI_def by simp
        then have "(AI, XI) \<in> Q_I_pos" by (metis \<open>(A, X) \<in> filterQuery I Q\<close> assms(5) image_eqI projectQuery.elims)
        then have "restrict AI zI \<in> XI" using \<open>wf_tuple n I zI \<and> (\<forall>(A, X)\<in>Q_I_pos. restrict A zI \<in> X)\<close> by blast
        obtain AJ XJ where "(AJ, XJ) = projectTable J (semiJoin (A, X) (I, zI))" by simp
        then have "AJ = A \<inter> J" by auto
        then have "(AJ, XJ) \<in> NQ_pos"
          using \<open>(A, X) \<in> Q_J_pos\<close> \<open>(AJ, XJ) = projectTable J (semiJoin (A, X) (I, zI))\<close> \<open>zI = t\<close> image_iff
          using assms(9) by fastforce
        then have "restrict AJ zJ \<in> XJ"
          using \<open>wf_tuple n J zJ \<and> (\<forall>(A, X)\<in>NQ_pos. restrict A zJ \<in> X)\<close> by blast
        have "XJ = Set.image (restrict J) (Set.filter (isSameIntersection zI (A \<inter> I)) X)"
          using \<open>(AJ, XJ) = projectTable J (semiJoin (A, X) (I, zI))\<close> by auto
        then have "restrict AJ zJ \<in> Set.image (restrict J) (Set.filter (isSameIntersection zI (A \<inter> I)) X)"
          using \<open>restrict AJ zJ \<in> XJ\<close> by blast
        moreover have "table n A X"
          using \<open>(A, X) \<in> Q\<close> assms(17) rwf_query_def wf_atable_def wf_query_def by fastforce
        moreover have "A \<subseteq> I \<union> J" using \<open>A \<subseteq> V\<close> assms(1) by auto
        then show ?thesis using restrict_merge[of zI I z zJ J A X n] AI_def True XI_def \<open>AJ = A \<inter> J\<close>
            \<open>restrict AI zI \<in> XI\<close> \<open>restrict I z = t\<close> \<open>restrict J z = xx\<close> \<open>wf_tuple n V z\<close> assms(1)
            assms(14) assms(17) calculation(2) calculation(3) rwf_query_def wf_query_def zI_def zJ_def by blast
      next
        case False
        have "(A, X) \<in> Q_J_pos" using \<open>(A, X) \<in> Q\<close> \<open>1 \<le> card (A \<inter> J)\<close> assms(6) assms(17)
            rwf_query_def set_filterQuery by fastforce
        moreover have "A \<subseteq> J"
          by (metis False One_nat_def Set.is_empty_def Suc_leI Suc_le_lessD \<open>1 \<le> card A\<close> \<open>A \<subseteq> V\<close>
              assms(1) assms(2) card_gt_0_iff finite_Int inf.absorb_iff2 inf_commute sup_commute sup_inf_absorb sup_inf_distrib1)
        then have "restrict A z = restrict A xx" using \<open>restrict J z = xx\<close> nested_include_restrict by blast
        define zI where "zI = restrict I z"
        define zJ where "zJ = restrict J z"
        have "zJ = xx" by (simp add: \<open>restrict J z = xx\<close> zJ_def)
        have "zI = t" by (simp add: \<open>restrict I z = t\<close> zI_def)
        have "z = merge zJ zI" by (simp add: \<open>zI = t\<close> \<open>zJ = xx\<close> assms(14))
        obtain AA XX where "(AA, XX) = projectTable J (semiJoin (A, X) (I, t))" by simp
        have "AA = A \<inter> J"
          using \<open>(AA, XX) = projectTable J (semiJoin (A, X) (I, t))\<close> by auto
        have "(AA, XX) \<in> NQ_pos"
          using \<open>(AA, XX) = projectTable J (semiJoin (A, X) (I, t))\<close> calculation image_iff assms(9)
            by fastforce
        then have "restrict AA zJ \<in> XX"
          using \<open>(AA, XX) \<in> NQ_pos\<close> \<open>\<forall>(A, X)\<in>NQ_pos. restrict A xx \<in> X\<close> \<open>zJ = xx\<close> by blast
        then have "restrict A z = restrict A zJ" by (simp add: \<open>restrict A z = restrict A xx\<close> \<open>zJ = xx\<close>)
        moreover have "restrict AA zJ = restrict A zJ" by (simp add: \<open>A \<subseteq> J\<close> \<open>AA = A \<inter> J\<close> inf.absorb1)
        then have "restrict A z \<in> XX" using \<open>restrict AA zJ \<in> XX\<close> calculation(2) by auto
        moreover have "XX \<subseteq> Set.image (restrict J) X"
        proof -
          obtain AAA XXX where "(AAA, XXX) = semiJoin (A, X) (I, t)" by simp
          then have "XXX \<subseteq> X" by auto
          then have "XX = Set.image (restrict J) XXX"
            using \<open>(AA, XX) = projectTable J (semiJoin (A, X) (I, t))\<close> \<open>(AAA, XXX) = semiJoin (A, X) (I, t)\<close> by auto
          then show ?thesis by (simp add: \<open>XXX \<subseteq> X\<close> image_mono)
        qed
        then have "restrict A z \<in> Set.image (restrict J) X" using calculation(3) by blast
        obtain zz where "restrict A z = restrict J zz" "zz \<in> X"
          using \<open>restrict A z \<in> restrict J ` X\<close> by blast
        then have "restrict A z = restrict A zz"
          by (metis Int_absorb2 \<open>A \<subseteq> J\<close> restrict_nested subset_refl)
        moreover have "restrict A zz = zz"
        proof -
          have "(A, X) \<in> Q" by (simp add: \<open>(A, X) \<in> Q\<close>)
          then have "table n A X" using assms(17) rwf_query_def wf_atable_def wf_query_def by fastforce
          then have "wf_tuple n A zz" using \<open>zz \<in> X\<close> table_def by blast
          then show ?thesis using restrict_idle by blast
        qed
        then have "restrict A zz = zz" using \<open>restrict A z = restrict J zz\<close> calculation(4) by auto
        then show ?thesis by (simp add: \<open>zz \<in> X\<close> calculation(4))
      qed
    qed
  qed
  then show ?thesis using calculation by blast
qed

lemma simple_set_inter:
  assumes "I \<subseteq> (\<Union>X\<in>A. f X)"
  shows "I \<subseteq> (\<Union>X\<in>A. (f X) \<inter> I)"
proof -
  have "\<And>x. x \<in> I \<Longrightarrow> x \<in> (\<Union>X\<in>A. (f X) \<inter> I)"
  proof -
    fix x assume "x \<in> I"
    obtain X where "X \<in> A" "x \<in> f X" using \<open>x \<in> I\<close> assms by auto
    then show "x \<in> (\<Union>X\<in>A. (f X) \<inter> I)" using \<open>x \<in> I\<close> by blast
  qed
  then show ?thesis by (simp add: subsetI)
qed

lemma union_restrict:
  assumes "restrict I z1 = restrict I z2"
  assumes "restrict J z1 = restrict J z2"
  shows "restrict (I \<union> J) z1 = restrict (I \<union> J) z2"
proof -
  define zz1 where "zz1 = restrict (I \<union> J) z1"
  define zz2 where "zz2 = restrict (I \<union> J) z2"
  have "length z1 = length z2" by (metis assms(2) length_restrict)
  have "\<And>i. i < length z1 \<Longrightarrow> zz1!i = zz2!i"
  proof -
    fix i assume "i < length z1"
    then show "zz1!i = zz2!i"
    proof (cases "i \<in> I")
      case True
      then show ?thesis
        by (metis simple_restrict_none \<open>i < length z1\<close> \<open>length z1 = length z2\<close> assms(1)
            nth_restrict zz1_def zz2_def)
    next
      case False
      then show ?thesis
        by (metis simple_restrict_none UnE \<open>i < length z1\<close> \<open>length z1 = length z2\<close> assms(2)
            nth_restrict zz1_def zz2_def)
    qed
  qed
  then have "\<forall>i < length z1. (restrict (I \<union> J) z1)!i = (restrict (I \<union> J) z2)!i"
    using zz1_def zz2_def by blast
  then show ?thesis
    by (simp add: simple_list_index_equality \<open>length z1 = length z2\<close>)
qed

lemma partial_correctness_direct:
  assumes "V = I \<union> J"
  assumes "Set.is_empty (I \<inter> J)"
  assumes "card I \<ge> 1"
  assumes "card J \<ge> 1"
  assumes "Q_I_pos = projectQuery I (filterQuery I Q)"
  assumes "Q_J_pos = filterQuery J Q"
  assumes "Q_I_neg = filterQueryNeg I Qn"
  assumes "Q_J_neg = filterQuery J (Qn - Q_I_neg)"
  assumes "R_I = genericJoin I Q_I_pos Q_I_neg"
  assumes "X = {(t, genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))) | t . t \<in> R_I}"
  assumes "R = (\<Union>(t, x) \<in> X. {merge xx t | xx . xx \<in> x})"
  assumes "R_NQ = genericJoin J NQ_pos NQ_neg"
  assumes "\<forall>x. (x \<in> R_I \<longleftrightarrow> wf_tuple n I x \<and> (\<forall>(A, X)\<in>Q_I_pos. restrict A x \<in> X) \<and> (\<forall>(A, X)\<in>Q_I_neg. restrict A x \<notin> X))"
  assumes "\<forall>t\<in>R_I. (\<forall>y. (y \<in> genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t)) \<longleftrightarrow> wf_tuple n J y \<and>
  (\<forall>(A, X)\<in>(newQuery J Q_J_pos (I, t)). restrict A y \<in> X) \<and> (\<forall>(A, X)\<in>(newQuery J Q_J_neg (I, t)). restrict A y \<notin> X)))"
  assumes "wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)"
  assumes "rwf_query n V Q Qn"
  shows "z \<in> R"
proof -
  define CI where "CI = filterQuery I Q"
  define zI where "zI = restrict I z"
  have "wf_tuple n I zI"
    using assms(1) assms(15) wf_tuple_restrict_simple zI_def by auto
  have "\<And>A X. ((A, X)\<in>Q_I_pos \<Longrightarrow> restrict A zI \<in> X)"
  proof -
    fix A X assume "(A, X)\<in>Q_I_pos"
    have "(A, X) \<in> projectQuery I Q" using \<open>(A, X) \<in> Q_I_pos\<close> assms(5) by auto
    then obtain AA XX where "X = Set.image (restrict I) XX" "(AA, XX) \<in> Q" "A = AA \<inter> I" by auto
    moreover have "(restrict AA z) \<in> XX" using assms(15) calculation(2) by blast
    then have "restrict I (restrict AA z) \<in> X" by (simp add: calculation(1))
    then show "restrict A zI \<in> X"
      by (metis calculation(3) inf.right_idem inf_commute restrict_nested zI_def)
  qed
  moreover have "\<And>A X. ((A, X)\<in>Q_I_neg \<Longrightarrow> restrict A zI \<notin> X)"
  proof -
    fix A X assume "(A, X)\<in>Q_I_neg"
    then have "(A, X) \<in> Qn" by (simp add: assms(7))
    then have "restrict A z \<notin> X" using assms(15) by blast
    moreover have "A \<subseteq> I" using \<open>(A, X) \<in> Q_I_neg\<close> assms(7) by auto
    then have "restrict A z = restrict A zI"
      using nested_include_restrict zI_def by metis
    then show "restrict A zI \<notin> X" using calculation by auto
  qed
  then have "zI \<in> R_I" using \<open>wf_tuple n I zI\<close> assms(13) calculation by auto
  define zJ where "zJ = restrict J z"
  have "wf_tuple n J zJ" using assms(1) assms(15) wf_tuple_restrict_simple zJ_def by auto
  have "\<And>A X. ((A, X)\<in>Q_J_pos \<Longrightarrow> restrict A z \<in> X)" using assms(15) assms(6) by auto
  define NQ where "NQ = newQuery J Q_J_pos (I, zI)"
  have "\<And>A X. ((A, X)\<in>Q_J_pos \<Longrightarrow> (isSameIntersection zI (A \<inter> I) (restrict A z)))"
  proof -
    fix A X assume "(A, X) \<in> Q_J_pos"
    obtain "wf_set n V" "wf_tuple n I zI" using \<open>wf_tuple n I zI\<close> assms(16) rwf_query_def wf_query_def by blast
    moreover have "A \<subseteq> V"
    proof -
      have "included V Q_J_pos"
        by (metis filterQuery.elims assms(16) assms(6) included_def member_filter rwf_query_def)
      then show ?thesis using \<open>(A, X) \<in> Q_J_pos\<close> included_def by fastforce
    qed
    moreover have "wf_tuple n A (restrict A z)" by (meson assms(15) calculation(3) wf_tuple_restrict_simple)
    then show "isSameIntersection zI (A \<inter> I) (restrict A z)"
      using isSame_equi_dev[of n V I zI A "restrict A z" "A \<inter> I"]
      by (metis nested_include_restrict assms(1) calculation(1) calculation(2) calculation(3) inf_le1 inf_le2 sup_ge1 zI_def)
  qed
  then have "\<And>A X. ((A, X)\<in>NQ \<Longrightarrow> restrict A zJ \<in> X)"
  proof -
    fix A X assume "(A, X)\<in>NQ"
    obtain AA XX where "(A, X) = projectTable J (semiJoin (AA, XX) (I, zI))" "(AA, XX) \<in> Q_J_pos"
      using NQ_def \<open>(A, X) \<in> NQ\<close> by auto
    then have "restrict AA z \<in> XX" using \<open>\<And>X A. (A, X) \<in> Q_J_pos \<Longrightarrow> restrict A z \<in> X\<close> by blast
    then have "restrict AA z \<in> snd (semiJoin (AA, XX) (I, zI))"
      using \<open>(AA, XX) \<in> Q_J_pos\<close> \<open>\<And>X A. (A, X) \<in> Q_J_pos \<Longrightarrow> isSameIntersection zI (A \<inter> I) (restrict A z)\<close> by auto
    then have "restrict J (restrict AA z) \<in> X"
      using \<open>(A, X) = projectTable J (semiJoin (AA, XX) (I, zI))\<close> by auto
    then show "restrict A zJ \<in> X"
      by (metis \<open>(A, X) = projectTable J (semiJoin (AA, XX) (I, zI))\<close> fst_conv inf.idem inf_commute
          projectTable.simps restrict_nested semiJoin.simps zJ_def)
  qed
  moreover have "\<forall>y. (y \<in> genericJoin J (newQuery J Q_J_pos (I, zI)) (newQuery J Q_J_neg (I, zI)) \<longleftrightarrow> wf_tuple n J y \<and>
  (\<forall>(A, X)\<in>newQuery J Q_J_pos (I, zI). restrict A y \<in> X) \<and> (\<forall>(A, X)\<in>newQuery J Q_J_neg (I, zI). restrict A y \<notin> X))"
    using \<open>zI \<in> R_I\<close> assms(14) by auto
  then have "zJ \<in> genericJoin J (newQuery J Q_J_pos (I, zI)) (newQuery J Q_J_neg (I, zI))
                     \<longleftrightarrow> wf_tuple n J zJ \<and> (\<forall>(A, X)\<in>newQuery J Q_J_pos (I, zI). restrict A zJ \<in> X) \<and>
  (\<forall>(A, X)\<in>newQuery J Q_J_neg (I, zI). restrict A zJ \<notin> X)" by blast
  moreover have "\<forall>(A, X)\<in>newQuery J Q_J_pos (I, zI). restrict A zJ \<in> X"
    using NQ_def calculation(2) by blast
  moreover have "\<And>A X. (A, X)\<in>newQuery J Q_J_neg (I, zI) \<Longrightarrow> restrict A zJ \<notin> X"
  proof -
    fix A X assume "(A, X) \<in> newQuery J Q_J_neg (I, zI)"
    then have "(A, X) \<in> (Set.image (\<lambda>tab. projectTable J (semiJoin tab (I, zI))) Q_J_neg)"
      using newQuery.simps by blast
    then obtain AA XX where "(A, X) = projectTable J (semiJoin (AA, XX) (I, zI))" and "(AA, XX) \<in> Q_J_neg"
      by auto
    then have "A = AA \<inter> J" by auto
    then have "(AA, XX) \<in> Qn" using \<open>(AA, XX) \<in> Q_J_neg\<close> assms(8) by auto
    then have "restrict AA z \<notin> XX" using assms(15) by blast
    show "restrict A zJ \<notin> X"
    proof (rule ccontr)
      assume "\<not> (restrict A zJ \<notin> X)"
      then have "restrict A zJ \<in> X" by simp
      then have "restrict A zJ \<in> Set.image (restrict J) (Set.filter (isSameIntersection zI (I \<inter> AA)) XX)"
        by (metis projectTable.simps semiJoin.simps \<open>(A, X) = projectTable J (semiJoin (AA, XX) (I, zI))\<close>
            inf_commute snd_conv)
      then obtain zz where "restrict A zJ = restrict J zz" and "zz \<in> (Set.filter (isSameIntersection zI (I \<inter> AA)) XX)"
        by blast
      moreover have "restrict A zJ = restrict AA zJ"
        by (simp add: restrict_nested \<open>A = AA \<inter> J\<close> zJ_def)
      then have "restrict AA z = zz"
      proof -
        have "restrict J (restrict AA zz) = restrict J (restrict AA z)"
          by (metis (no_types, lifting) restrict_nested \<open>restrict A zJ = restrict AA zJ\<close>
              calculation(1) inf_commute inf_left_idem zJ_def)
        moreover have "isSameIntersection zI (I \<inter> AA) zz"
          using \<open>zz \<in> Set.filter (isSameIntersection zI (I \<inter> AA)) XX\<close> by auto
        moreover have "wf_tuple n AA zz"
        proof -
          have "rwf_query n V Q Qn" by (simp add: assms(16))
          moreover have "(AA, XX) \<in> Q \<union> Qn" by (simp add: \<open>(AA, XX) \<in> Qn\<close>)
          then have "wf_atable n (AA, XX)" using calculation rwf_query_def wf_query_def by blast
          then show ?thesis
            using \<open>zz \<in> Set.filter (isSameIntersection zI (I \<inter> AA)) XX\<close> table_def wf_atable_def by fastforce
        qed
        moreover have "restrict AA zz = zz" using calculation(3) restrict_idle by blast
        moreover have "AA \<subseteq> V"
        proof -
          have "included V Qn" using assms(16) rwf_query_def by blast
          then show ?thesis using \<open>(AA, XX) \<in> Qn\<close> included_def by fastforce
        qed
        moreover have "wf_set n V" using assms(16) rwf_query_def wf_query_def by blast
        moreover have "restrict (I \<inter> AA) zz = restrict (I \<inter> AA) zI"
          using isSame_equi_dev[of n V AA zz V z "I \<inter> AA"]
          by (metis (mono_tags, lifting) isSame_equi_dev \<open>wf_tuple n I zI\<close> assms(1)
              calculation(2) calculation(3) calculation(5) calculation(6) inf_le1 inf_le2 sup_ge1)
        then have "restrict I (restrict AA zz) = restrict I (restrict AA z)"
          by (metis (mono_tags, lifting) restrict_nested inf_le1 nested_include_restrict zI_def)
        then have "restrict (I \<union> J) (restrict AA z) = restrict (I \<union> J) (restrict AA zz)"
          using union_restrict calculation(1) by fastforce
        moreover have "AA \<subseteq> I \<union> J"
          by (metis \<open>(AA, XX) \<in> Qn\<close> assms(1) assms(16) case_prodD included_def rwf_query_def)
        then show ?thesis
          by (metis restrict_nested calculation(4) calculation(7) inf.absorb_iff2)
      qed
      then show "False" using \<open>restrict AA z \<notin> XX\<close> calculation(2) by auto
    qed
  qed
  then have "zJ \<in> genericJoin J (newQuery J Q_J_pos (I, zI)) (newQuery J Q_J_neg (I, zI))"
    using \<open>wf_tuple n J zJ\<close> calculation(3) calculation(4) by blast
  have "z = merge zJ zI"
    using restrict_partition_merge assms(1) assms(15) assms(2) zI_def zJ_def by fastforce
  moreover have "(zI, genericJoin J (newQuery J Q_J_pos (I, zI)) (newQuery J Q_J_neg (I, zI))) \<in> X"
    using \<open>zI \<in> R_I\<close> assms(10) by blast
  then show ?thesis
    using \<open>zJ \<in> genericJoin J (newQuery J Q_J_pos (I, zI)) (newQuery J Q_J_neg (I, zI))\<close> assms(11)
      calculation(5) by blast
qed

lemma obvious_forall:
  assumes "\<forall>x\<in>X. P x"
  assumes "x\<in>X"
  shows "P x"
  by (simp add: assms(1) assms(2))

lemma correctness:
  "\<lbrakk>rwf_query n V Q Qn; card V \<ge> 1\<rbrakk> \<Longrightarrow> (z \<in> genericJoin V Q Qn \<longleftrightarrow> wf_tuple n V z \<and>
  (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X))"
proof (induction V Q Qn arbitrary: z rule: genericJoin.induct)
  case (1 V Q Qn)
    then show ?case
    proof (cases "card V \<le> 1")
      case True
      have "card V = 1" using "1.prems"(2) True le_antisym by blast
      then show ?thesis using base_correctness[of V n Q Qn "genericJoin V Q Qn" z] using "1.prems"(1) by blast
    next
      case False
      obtain I J where "(I, J) = getIJ Q Qn V" by (metis surj_pair)
      define Q_I_pos where "Q_I_pos = projectQuery I (filterQuery I Q)"
      define Q_I_neg where "Q_I_neg = filterQueryNeg I Qn"
      define R_I where "R_I = genericJoin I Q_I_pos Q_I_neg"
      define Q_J_neg where "Q_J_neg = filterQuery J (Qn - Q_I_neg)"
      define Q_J_pos where "Q_J_pos = filterQuery J Q"
      define X where "X = {(t, genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))) | t . t \<in> R_I}"
      define R where "R = (\<Union>(t, x) \<in> X. {merge xx t | xx . xx \<in> x})"
      then have "R = genericJoin V Q Qn"
        using vars_genericJoin[of V I J Q Qn Q_I_pos Q_I_neg R_I Q_J_neg Q_J_pos X R]
        by (metis "1.prems"(1) False Q_I_neg_def Q_I_pos_def Q_J_neg_def Q_J_pos_def R_I_def Suc_1 X_def
            \<open>(I, J) = getIJ Q Qn V\<close> not_less_eq_eq)
      obtain "rwf_query n I Q_I_pos Q_I_neg" and "card I \<ge> 1"
        by (metis "1.prems"(1) False Q_I_neg_def Q_I_pos_def Suc_1 \<open>(I, J) = getIJ Q Qn V\<close> getIJ.getIJProperties(1)
            getIJ.wf_firstRecursiveCall getIJ_axioms not_less_eq_eq)
      then have "\<forall>x. (x \<in> R_I \<longleftrightarrow>
  wf_tuple n I x \<and> (\<forall>(A, X)\<in>Q_I_pos. restrict A x \<in> X)  \<and> (\<forall>(A, X)\<in>Q_I_neg. restrict A x \<notin> X))"
        using "1.IH"(1) False Q_I_neg_def Q_I_pos_def R_I_def \<open>(I, J) = getIJ Q Qn V\<close> by auto
      moreover have "\<forall>t\<in>R_I. (\<forall>y. (y \<in> genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t)) \<longleftrightarrow> wf_tuple n J y \<and>
  (\<forall>(A, X)\<in>(newQuery J Q_J_pos (I, t)). restrict A y \<in> X) \<and> (\<forall>(A, X)\<in>(newQuery J Q_J_neg (I, t)). restrict A y \<notin> X)))"
      proof
        fix t assume "t \<in> R_I"
        have "card J \<ge> 1"
          by (metis False Suc_1 \<open>(I, J) = getIJ Q Qn V\<close> getIJProperties(2) le_SucE nat_le_linear)
        moreover have "rwf_query n J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))"
          by (metis "1.prems"(1) Diff_subset False Q_J_neg_def Q_J_pos_def Suc_1 \<open>(I, J) = getIJ Q Qn V\<close>
              getIJ.wf_secondRecursiveCalls getIJ_axioms not_less_eq_eq)
        define NQ_pos where "NQ_pos = newQuery J Q_J_pos (I, t)"
        define NQ_neg where "NQ_neg = newQuery J Q_J_neg (I, t)"
        have "\<And>y. y \<in> genericJoin J NQ_pos NQ_neg \<longleftrightarrow>
  wf_tuple n J y \<and> (\<forall>(A, X)\<in>NQ_pos. restrict A y \<in> X) \<and> (\<forall>(A, X)\<in>NQ_neg. restrict A y \<notin> X)"
        proof -
          fix y
          have "rwf_query n J NQ_pos NQ_neg"
            using NQ_neg_def NQ_pos_def \<open>rwf_query n J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))\<close> by blast
          then show "y \<in> genericJoin J NQ_pos NQ_neg \<longleftrightarrow>
  wf_tuple n J y \<and> (\<forall>(A, X)\<in>NQ_pos. restrict A y \<in> X) \<and> (\<forall>(A, X)\<in>NQ_neg. restrict A y \<notin> X)"
            using "1.IH"(2)[of "(I, J)" I J Q_I_pos Q_I_neg R_I Q_J_neg Q_J_pos t y]
            by (metis "1.prems"(1) False NQ_neg_def NQ_pos_def Q_I_neg_def Q_I_pos_def Q_J_neg_def
                Q_J_pos_def R_I_def Suc_1 \<open>(I, J) = getIJ Q Qn V\<close> calculation filter_Q_J_neg_same not_less_eq_eq)
        qed
        then show "\<forall>y. (y \<in> genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t)) \<longleftrightarrow> wf_tuple n J y \<and>
  (\<forall>(A, X)\<in>(newQuery J Q_J_pos (I, t)). restrict A y \<in> X) \<and> (\<forall>(A, X)\<in>(newQuery J Q_J_neg (I, t)). restrict A y \<notin> X))"
          using NQ_neg_def NQ_pos_def by blast
      qed
      moreover obtain "V = I \<union> J" "Set.is_empty (I \<inter> J)" "card I \<ge> 1" "card J \<ge> 1"
        by (metis False Set.is_empty_def Suc_1 \<open>(I, J) = getIJ Q Qn V\<close> coreProperties not_less_eq_eq)
      moreover have "rwf_query n V Q Qn" by (simp add: "1.prems"(1))
      then show ?thesis
      proof -
        have "z \<in> genericJoin V Q Qn \<Longrightarrow> wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)"
        proof -
          fix z assume "z \<in> genericJoin V Q Qn"
          have "z \<in> (\<Union>(t, x) \<in> X. {merge xx t | xx . xx \<in> x})"
            using R_def \<open>R = genericJoin V Q Qn\<close> \<open>z \<in> genericJoin V Q Qn\<close> by blast
          obtain t R_NQ where "z \<in> {merge xx t | xx . xx \<in> R_NQ}" "(t, R_NQ) \<in> X"
            using \<open>z \<in> (\<Union>(t, x)\<in>X. {merge xx t |xx. xx \<in> x})\<close> by blast
          then have "t \<in> R_I" using X_def by blast
          define NQ where "NQ = newQuery J Q_J_pos (I, t)"
          define NQ_neg where "NQ_neg = newQuery J Q_J_neg (I, t)"
          have "R_NQ = genericJoin J NQ NQ_neg" using NQ_def NQ_neg_def X_def \<open>(t, R_NQ) \<in> X\<close> by blast
          obtain xx where "z = merge xx t" "xx \<in> R_NQ"
            using \<open>z \<in> {merge xx t |xx. xx \<in> R_NQ}\<close> by blast
          have "\<forall>y. (y \<in> R_NQ \<longleftrightarrow> wf_tuple n J y \<and> (\<forall>(A, X)\<in>NQ. restrict A y \<in> X) \<and> (\<forall>(A, X)\<in>NQ_neg. restrict A y \<notin> X))"
          proof -
            have "\<forall>tt\<in>R_I. (\<forall>x. (x \<in> genericJoin J NQ NQ_neg
                         \<longleftrightarrow> wf_tuple n J x \<and> (\<forall>(A, X)\<in>NQ. restrict A x \<in> X) \<and> (\<forall>(A, X)\<in>NQ_neg. restrict A x \<notin> X)))"
              using NQ_def NQ_neg_def \<open>t \<in> R_I\<close> calculation(2) by auto
            moreover have "t\<in>R_I" by (simp add: \<open>t \<in> R_I\<close>)
            then have "(\<forall>x. (x \<in> genericJoin J NQ NQ_neg
                         \<longleftrightarrow> wf_tuple n J x \<and> (\<forall>(A, X)\<in>NQ. restrict A x \<in> X) \<and>  (\<forall>(A, X)\<in>NQ_neg. restrict A x \<notin> X)))"
              using obvious_forall[where ?x=t and ?X=R_I] calculation by fastforce
            then show ?thesis using \<open>R_NQ = genericJoin J NQ NQ_neg\<close> by blast
          qed
          show "wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)"
            using partial_correctness[of V I J Q_I_pos Q Q_J_pos Q_I_neg Qn Q_J_neg NQ t NQ_neg R_NQ R_I n z xx]
            using "1.prems"(1) NQ_def NQ_neg_def Q_I_neg_def Q_I_pos_def Q_J_neg_def Q_J_pos_def
              \<open>R_NQ = genericJoin J NQ NQ_neg\<close> \<open>\<forall>y. (y \<in> R_NQ) = (wf_tuple n J y \<and> (\<forall>(A, X)\<in>NQ. restrict A y \<in> X) \<and> (\<forall>(A, X)\<in>NQ_neg. restrict A y \<notin> X))\<close>
              \<open>t \<in> R_I\<close> \<open>xx \<in> R_NQ\<close> \<open>z = merge xx t\<close> calculation(1) calculation(3) calculation(4) calculation(5) calculation(6) by blast
        qed
        moreover have "wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X) \<Longrightarrow> z \<in> genericJoin V Q Qn"
        proof -
          fix z assume "wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)"
          have "z \<in> R"
            using partial_correctness_direct[of V I J Q_I_pos Q Q_J_pos Q_I_neg Qn Q_J_neg R_I X R
                _ _ _ n z]
            "1.prems"(1) Q_I_neg_def Q_I_pos_def Q_J_neg_def Q_J_pos_def R_I_def R_def X_def
              \<open>1 \<le> card I\<close> \<open>1 \<le> card J\<close> \<open>Set.is_empty (I \<inter> J)\<close> \<open>V = I \<union> J\<close>
              \<open>\<forall>t\<in>R_I. \<forall>y. (y \<in> genericJoin J (newQuery J Q_J_pos (I, t)) (newQuery J Q_J_neg (I, t))) = (wf_tuple n J y \<and> (\<forall>(A, X)\<in>newQuery J Q_J_pos (I, t). restrict A y \<in> X) \<and> (\<forall>(A, X)\<in>newQuery J Q_J_neg (I, t). restrict A y \<notin> X))\<close>
              \<open>\<forall>x. (x \<in> R_I) = (wf_tuple n I x \<and> (\<forall>(A, X)\<in>Q_I_pos. restrict A x \<in> X) \<and> (\<forall>(A, X)\<in>Q_I_neg. restrict A x \<notin> X))\<close>
              \<open>wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)\<close> by blast
          then show "z \<in> genericJoin V Q Qn" using \<open>R = genericJoin V Q Qn\<close> by blast
        qed
        then show ?thesis using calculation by linarith
      qed
  qed
qed

lemma wf_set_finite:
  assumes "wf_set n A"
  shows "finite A"
  using assms finite_nat_set_iff_bounded wf_set_def by auto

lemma vars_wrapperGenericJoin:
  fixes Q :: "'a query" and Q_pos :: "'a query" and Q_neg :: "'a query"
  and V :: "nat set" and Qn :: "'a query"
  assumes "Q = Set.filter (\<lambda>(A, _). \<not> Set.is_empty A) Q_pos"
      and "V = (\<Union>(A, X)\<in>Q. A)"
      and "Qn = Set.filter (\<lambda>(A, _). A \<subseteq> V \<and> card A \<ge> 1) Q_neg"
      and "\<not> Set.is_empty Q"
      and "\<not>((\<exists>(A, X)\<in>Q_pos. Set.is_empty X) \<or> (\<exists>(A, X)\<in>Q_neg. Set.is_empty A \<and> \<not> Set.is_empty X))"
    shows "wrapperGenericJoin Q_pos Q_neg = genericJoin V Q Qn"
  using assms wrapperGenericJoin.simps
proof -
  let ?r = "wrapperGenericJoin Q_pos Q_neg"
  have "?r = (if ((\<exists>(A, X)\<in>Q_pos. Set.is_empty X) \<or> (\<exists>(A, X)\<in>Q_neg. Set.is_empty A \<and> \<not> Set.is_empty X)) then
      {}
    else
      let Q = Set.filter (\<lambda>(A, _). \<not> Set.is_empty A) Q_pos in
      if Set.is_empty Q then
        (\<Inter>(A, X)\<in>Q_pos. X) -  (\<Union>(A, X)\<in>Q_neg. X)
      else
        let V = (\<Union>(A, X)\<in>Q. A) in
        let Qn = Set.filter (\<lambda>(A, _). A \<subseteq> V \<and> card A \<ge> 1) Q_neg in
        genericJoin V Q Qn)" by simp
  also have "... = (let Q = Set.filter (\<lambda>(A, _). \<not> Set.is_empty A) Q_pos in
      if Set.is_empty Q then
        (\<Inter>(A, X)\<in>Q_pos. X) -  (\<Union>(A, X)\<in>Q_neg. X)
      else
        let V = (\<Union>(A, X)\<in>Q. A) in
        let Qn = Set.filter (\<lambda>(A, _). A \<subseteq> V \<and> card A \<ge> 1) Q_neg in
        genericJoin V Q Qn)" using assms(5) by simp
  moreover have "\<not> (let Q = Set.filter (\<lambda>(A, _). \<not> Set.is_empty A) Q_pos in Set.is_empty Q)"
    using assms(1) assms(4) by auto
  ultimately have "(let Q = Set.filter (\<lambda>(A, _). \<not> Set.is_empty A) Q_pos in
      if Set.is_empty Q then
        (\<Inter>(A, X)\<in>Q_pos. X) -  (\<Union>(A, X)\<in>Q_neg. X)
      else
        let V = (\<Union>(A, X)\<in>Q. A) in
        let Qn = Set.filter (\<lambda>(A, _). A \<subseteq> V \<and> card A \<ge> 1) Q_neg in
        genericJoin V Q Qn) = (let Q = Set.filter (\<lambda>(A, _). \<not> Set.is_empty A) Q_pos in
        let V = (\<Union>(A, X)\<in>Q. A) in
        let Qn = Set.filter (\<lambda>(A, _). A \<subseteq> V \<and> card A \<ge> 1) Q_neg in
        genericJoin V Q Qn)" by presburger
  also have "... = (genericJoin V Q Qn)" using assms(1) assms(2) assms(3) by metis
  then show ?thesis using wrapperGenericJoin.simps assms(5) calculation by simp
qed

lemma wrapper_correctness:
  assumes "card Q_pos \<ge>1"
  assumes "\<forall>(A, X)\<in>(Q_pos \<union> Q_neg). table n A X \<and> wf_set n A"
  shows "z \<in> wrapperGenericJoin Q_pos Q_neg \<longleftrightarrow> wf_tuple n (\<Union>(A, X)\<in>Q_pos. A) z \<and> (\<forall>(A, X)\<in>Q_pos. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg. restrict A z \<notin> X)"
proof (cases "(\<exists>(A, X)\<in>Q_pos. Set.is_empty X) \<or> (\<exists>(A, X)\<in>Q_neg. Set.is_empty A \<and> \<not> Set.is_empty X)")
  let ?r = "wrapperGenericJoin Q_pos Q_neg"
  case True
  then have "?r = {}" using wrapperGenericJoin.simps by simp
  have "\<not> (wf_tuple n (\<Union>(A, X)\<in>Q_pos. A) z \<and> (\<forall>(A, X)\<in>Q_pos. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg. restrict A z \<notin> X))"
  proof (rule notI)
    assume "wf_tuple n (\<Union>(A, X)\<in>Q_pos. A) z \<and> (\<forall>(A, X)\<in>Q_pos. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg. restrict A z \<notin> X)"
    then show "False"
    proof (cases "\<exists>(A, X)\<in>Q_pos. Set.is_empty X")
      case True
      then show ?thesis
        using \<open>wf_tuple n (\<Union>(A, X)\<in>Q_pos. A) z \<and> (\<forall>(A, X)\<in>Q_pos. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg. restrict A z \<notin> X)\<close>
        by (metis (no_types, lifting) Set.is_empty_def case_prod_beta' empty_iff)
    next
      let ?v = "replicate n None"
      case False
      then have "\<exists>(A, X)\<in>Q_neg. Set.is_empty A \<and> \<not> Set.is_empty X" using True by blast
      then obtain A X where "(A, X) \<in> Q_neg" "Set.is_empty A" "\<not> Set.is_empty X" by auto
      then have "table n A X" using assms(2) by auto
      then have "X \<subseteq> {?v}" using \<open>Set.is_empty A\<close> table_empty unit_table_def
        by (metis Set.is_empty_def \<open>\<not> Set.is_empty X\<close> empty_table_def set_eq_subset)
      then show ?thesis using \<open>(A, X) \<in> Q_neg\<close> \<open>Set.is_empty A\<close> \<open>\<not> Set.is_empty X\<close>
          \<open>wf_tuple n (\<Union>(A, X)\<in>Q_pos. A) z \<and> (\<forall>(A, X)\<in>Q_pos. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg. restrict A z \<notin> X)\<close>
        by (metis (no_types, lifting) Set.is_empty_def \<open>table n A X\<close> case_prod_beta' empty_table_def
            in_unit_table inf_le1 inf_le2 prod.sel(1) snd_conv subset_empty table_empty wf_tuple_restrict_simple)
    qed
  qed
  then show ?thesis using \<open>?r = {}\<close> by simp
next
  case False
  then have forall: "(\<forall>(A, X)\<in>Q_pos. \<not> Set.is_empty X) \<and> (\<forall>(A, X)\<in>Q_neg. \<not> Set.is_empty A \<or> Set.is_empty X)" by auto
  define Q where "Q = Set.filter (\<lambda>(A, _). \<not> Set.is_empty A) Q_pos"
  define V where "V = (\<Union>(A, X)\<in>Q. A)"
  let ?r = "wrapperGenericJoin Q_pos Q_neg"
  show ?thesis
  proof (cases "Q = {}")
    case True
    then have r_def: "?r = (\<Inter>(A, X)\<in>Q_pos. X) -  (\<Union>(A, X)\<in>Q_neg. X)" using Q_def Set.is_empty_def False by auto
    moreover have empty_u: "(\<Union>(A, X)\<in>Q_pos. A) = {}"
      by (metis (no_types, lifting) Q_def SUP_bot_conv(2) Set.is_empty_def True case_prod_beta' empty_iff member_filter)
    then have "V = {}" using True V_def by blast
    moreover have "\<And>A X. (A, X) \<in> Q_pos \<Longrightarrow> X \<subseteq> {replicate n None}"
    proof -
      fix A X assume "(A, X) \<in> Q_pos"
      then have "table n A X" using assms(2) by auto
      then have "A = {}"
      proof -
        have "(A, X) \<notin> Q" by (simp add: True)
        then show ?thesis by (simp add: Q_def Set.is_empty_def \<open>(A, X) \<in> Q_pos\<close>)
      qed
      then show "X \<subseteq> {replicate n None}" using \<open>A = {}\<close> \<open>table n A X\<close> table_empty unit_table_def by fastforce
    qed
    have "?r \<subseteq> {replicate n None}"
    proof (rule subsetI)
      fix x assume "x \<in> ?r"
      obtain A X where "(A, X) \<in> Q_pos" using \<open>card Q_pos \<ge> 1\<close>
        using True card.empty not_one_le_zero by (metis bot.extremum_uniqueI subrelI)
      then have "x \<in> X" using \<open>x \<in> ?r\<close> r_def by auto
      then show "x \<in> {replicate n None}" using \<open>(A, X) \<in> Q_pos\<close> \<open>\<And>X A. (A, X) \<in> Q_pos \<Longrightarrow> X \<subseteq> {replicate n None}\<close> by blast
    qed
    let ?v = "replicate n None"
    show ?thesis
    proof (cases "?r = {}")
      case True
      have disj: "\<exists>A X. ((A, X) \<in> Q_pos \<and> X = {}) \<or> ((A, X) \<in> Q_neg \<and> {?v} \<subseteq> X)"
      proof (rule ccontr)
        assume "\<nexists>A X. (A, X) \<in> Q_pos \<and> X = {} \<or> (A, X) \<in> Q_neg \<and> {?v} \<subseteq> X"
        then have x_pos: "\<forall>(A, X)\<in>Q_pos. X = {?v}" using \<open>\<And>X A. (A, X) \<in> Q_pos \<Longrightarrow> X \<subseteq> {replicate n None}\<close> by blast
        moreover have x_neg: "\<forall>(A, X)\<in>Q_neg. ?v \<notin> X" using \<open>\<nexists>A X. (A, X) \<in> Q_pos \<and> X = {} \<or> (A, X) \<in> Q_neg \<and> {replicate n None} \<subseteq> X\<close> by blast
        ultimately have "?v \<in> ?r" using r_def
        proof -
          have "?v \<in> (\<Inter>(A, X)\<in>Q_pos. X)" using x_pos by auto
          moreover have "?v \<notin> (\<Union>(A, X)\<in>Q_neg. X)" using x_neg by auto
          ultimately show ?thesis using r_def by auto
        qed
        then show "False" using True by blast
      qed
      have "\<not> (wf_tuple n (\<Union>(A, X)\<in>Q_pos. A) z \<and> (\<forall>(A, X)\<in>Q_pos. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg. restrict A z \<notin> X))"
      proof (rule notI)
        assume "wf_tuple n (\<Union>(A, X)\<in>Q_pos. A) z \<and> (\<forall>(A, X)\<in>Q_pos. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg. restrict A z \<notin> X)"
        have "z = ?v"
          using \<open>wf_tuple n (\<Union>(A, X)\<in>Q_pos. A) z \<and> (\<forall>(A, X)\<in>Q_pos. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg. restrict A z \<notin> X)\<close> empty_u wf_tuple_empty by auto
        then have "\<And>A. restrict A z = z"
          by (metis getIJ.restrict_index_out getIJ_axioms length_replicate length_restrict nth_replicate nth_restrict simple_list_index_equality)
        then have "(\<exists>(A, X)\<in>Q_pos. z \<notin> X) \<or> (\<exists>(A, X)\<in>Q_neg. z \<in> X)" using disj using \<open>z = replicate n None\<close> by auto
        then show "False"
          using \<open>\<And>A. restrict A z = z\<close> \<open>wf_tuple n (\<Union>(A, X)\<in>Q_pos. A) z \<and> (\<forall>(A, X)\<in>Q_pos. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg. restrict A z \<notin> X)\<close> by auto
      qed
      then show ?thesis using True by blast
    next
      case False
      then have "?r = {?v}" using \<open>wrapperGenericJoin Q_pos Q_neg \<subseteq> {replicate n None}\<close> by blast
      then have "\<And>A X. (A, X) \<in> Q_pos \<Longrightarrow> X = {?v}"
          using Set.is_empty_def \<open>\<And>X A. (A, X) \<in> Q_pos \<Longrightarrow> X \<subseteq> {replicate n None}\<close> forall by fastforce
      then have "\<forall>(A, X)\<in>Q_pos. X = {?v}" by blast
      moreover have "\<forall>(A, X)\<in>Q_neg. ?v \<notin> X" using \<open>wrapperGenericJoin Q_pos Q_neg = {replicate n None}\<close> r_def by auto
      ultimately show ?thesis (is "?a \<longleftrightarrow> ?b")
      proof -
        have "?a \<Longrightarrow> ?b"
        proof -
          assume "?a"
          then have "z = ?v" using \<open>wrapperGenericJoin Q_pos Q_neg = {replicate n None}\<close> by blast
          then have "\<And>A. restrict A z = z"
            by (metis getIJ.restrict_index_out getIJ_axioms length_replicate length_restrict nth_replicate nth_restrict simple_list_index_equality)
          then show "?b" using \<open>\<forall>(A, X)\<in>Q_neg. replicate n None \<notin> X\<close> \<open>\<forall>(A, X)\<in>Q_pos. X = {replicate n None}\<close>
              \<open>z = replicate n None\<close> empty_u wf_tuple_empty by fastforce
        qed
        moreover have "?b \<Longrightarrow> ?a"
          using \<open>wrapperGenericJoin Q_pos Q_neg = {replicate n None}\<close> empty_u wf_tuple_empty by auto
        ultimately show ?thesis by blast
      qed
    qed
  next
    case False
    then have False_prev: "Q \<noteq> {}" by simp
    have "covering V Q" using V_def covering_def by blast
    moreover have "included V Q" using included_def V_def by fastforce
    define Qn where "Qn = Set.filter (\<lambda>(A, _). A \<subseteq> V \<and> card A \<ge> 1) Q_neg"
    then have "Qn \<subseteq> Q_neg" by auto
    moreover have "wf_query n V Q Qn"
    proof -
      have "wf_set n V"
      proof -
        have "\<And>x. x \<in> V \<Longrightarrow> x < n"
        proof -
          fix x assume "x \<in> V"
          obtain A X where "x \<in> A" "(A, X) \<in> Q" using V_def \<open>x \<in> V\<close> by blast
          then have "(A, X) \<in> (Q_pos \<union> Q_neg)" by (simp add: Q_def)
          then have "wf_set n A" using assms(2) by auto
          then show "x < n" using \<open>x \<in> A\<close> wf_set_def by blast
        qed
        then show ?thesis using wf_set_def by blast
      qed
      moreover have "card Q \<ge> 1"
      proof -
        have "finite Q_pos" using assms(1) not_one_le_zero by fastforce
        then have "finite Q" by (simp add: Q_def)
        then show ?thesis using False by (simp add: Suc_leI card_gt_0_iff)
      qed
      moreover have "\<And>Y. Y \<in> (Q \<union> Q_neg) \<Longrightarrow> wf_atable n Y"
      proof -
        fix Y assume "Y \<in> (Q \<union> Q_neg)"
        then obtain A X where "Y = (A, X)" by (meson case_prodE case_prodI2)
        then have "table n A X"
          by (metis (no_types, lifting) Q_def UnE Un_iff \<open>Y \<in> Q \<union> Q_neg\<close> assms(2) case_prodD member_filter sup_commute)
        moreover have "finite A"
        proof -
          have "wf_set n A"
            by (metis (no_types, lifting) Q_def UnE Un_iff \<open>Y = (A, X)\<close> \<open>Y \<in> Q \<union> Q_neg\<close> assms(2) case_prod_conv member_filter sup.commute)
          then show ?thesis using wf_set_finite by blast
        qed
        ultimately show "wf_atable n Y" by (simp add: \<open>Y = (A, X)\<close> wf_atable_def)
      qed
      ultimately have "wf_query n V Q Q_neg" using wf_query_def by blast
      then show ?thesis using Un_iff \<open>Qn \<subseteq> Q_neg\<close> subsetD wf_query_def
      proof -
        obtain pp :: "(nat set \<times> 'a option list set) set \<Rightarrow> (nat set \<times> 'a option list set) set \<Rightarrow> nat \<Rightarrow> nat set \<times> 'a option list set" where
          f1: "\<forall>n N P Pa. (wf_query n N P Pa \<or> \<not> 1 \<le> card P \<or> \<not> wf_set n N \<or> \<not> wf_atable n (pp Pa P n) \<and> pp Pa P n \<in> P \<union> Pa) \<and> (1 \<le> card P \<and> wf_set n N \<and> (\<forall>p. wf_atable n p \<or> p \<notin> P \<union> Pa) \<or> \<not> wf_query n N P Pa)"
          by (metis (full_types) wf_query_def)
        have "pp Qn Q n \<in> Qn \<longrightarrow> pp Qn Q n \<in> Q_neg"
          using \<open>Qn \<subseteq> Q_neg\<close> by blast
        then have "pp Qn Q n \<in> Q \<union> Q_neg \<or> wf_query n V Q Qn" using \<open>1 \<le> card Q\<close> \<open>wf_set n V\<close> f1 by auto
        then show ?thesis using \<open>1 \<le> card Q\<close> \<open>\<And>Y. Y \<in> Q \<union> Q_neg \<Longrightarrow> wf_atable n Y\<close> \<open>wf_set n V\<close> f1 by blast
      qed
    qed
    moreover have "non_empty_query Q"
    proof -
      have "\<And>A X. (A, X) \<in> Q \<Longrightarrow> card A \<ge> 1"
      proof -
        fix A X assume asm: "(A, X) \<in> Q"
        then have "wf_set n A"
          by (metis \<open>included V Q\<close> calculation(3) case_prodD included_def subsetD wf_query_def wf_set_def)
        then have "finite A" using wf_set_finite by blast
        then show "card A \<ge> 1"
          by (metis (no_types, lifting) One_nat_def Q_def Set.is_empty_def Suc_leI asm card_gt_0_iff case_prod_beta' member_filter prod.sel(1))
      qed
      then show ?thesis by (metis Q_def case_prodE fst_conv member_filter non_empty_query_def)
    qed
    moreover have "included V Qn" by (simp add: Qn_def case_prod_beta' included_def)
    moreover have "non_empty_query Qn" by (simp add: Qn_def case_prod_beta' non_empty_query_def)
    then have "rwf_query n V Q Qn"
      by (simp add: \<open>included V Q\<close> calculation(1) calculation(3) calculation(4) calculation(5) rwf_query_def)
    moreover have "card V \<ge> 1"
    proof -
      obtain A X where "(A, X) \<in> Q_pos" "\<not> Set.is_empty A" using False Q_def by force
      then have "A \<subseteq> V" by (metis Q_def \<open>included V Q\<close> included_def member_filter prod.simps(2))
      moreover have "finite V" using wf_set_finite \<open>wf_query n V Q Qn\<close> wf_query_def by blast
      ultimately show ?thesis
        by (metis One_nat_def Set.is_empty_def Suc_leI \<open>\<not> Set.is_empty A\<close> card_gt_0_iff subset_empty)
    qed
    then have "z \<in> genericJoin V Q Qn \<longleftrightarrow> wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)"
      using correctness[where ?n=n and ?V=V and ?Q=Q and ?z=z] by (simp add: calculation(6))
    moreover have "?r = genericJoin V Q Qn"
    proof -
      have "Qn = Set.filter (\<lambda>(A, _). A \<subseteq> V \<and> 1 \<le> card A) Q_neg" using Qn_def by blast
      moreover have "\<not> Set.is_empty Q" by (simp add: False_prev Set.is_empty_def)
      moreover have "\<not> ((\<exists>(A, X)\<in>Q_pos. Set.is_empty X) \<or> (\<exists>(A, X)\<in>Q_neg. Set.is_empty A \<and> \<not> Set.is_empty X))"
        using forall by blast
      ultimately show ?thesis using vars_wrapperGenericJoin[of Q Q_pos V Qn Q_neg] Q_def V_def by simp
    qed
    moreover have "z \<in> genericJoin V Q Qn \<Longrightarrow> (\<forall>(A, X)\<in>Q_pos - Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg - Qn. restrict A z \<notin> X)"
    proof -
      assume "z \<in> genericJoin V Q Qn"
      have "(\<And>A X. (A, X)\<in>Q_pos - Q \<Longrightarrow> restrict A z \<in> X)"
      proof -
        fix A X assume "(A, X) \<in> Q_pos - Q"
        then have "table n A X" using assms(2) by auto
        moreover have "Set.is_empty A"
          by (metis (no_types, lifting) DiffD1 DiffD2 Q_def \<open>(A, X) \<in> Q_pos - Q\<close> case_prod_beta' member_filter prod.sel(1))
        moreover have "\<not> Set.is_empty X" using forall using \<open>(A, X) \<in> Q_pos - Q\<close> by blast
        ultimately have "X = {replicate n None}" by (simp add: Set.is_empty_def empty_table_def table_empty unit_table_def)
        moreover have "wf_tuple n V z"
          using \<open>(z \<in> genericJoin V Q Qn) = (wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X))\<close> \<open>z \<in> genericJoin V Q Qn\<close> by linarith
        then have "restrict A z = replicate n None"
          using \<open>Set.is_empty A\<close> wf_tuple_empty wf_tuple_restrict_simple
          by (metis Diff_Int2 Diff_Int_distrib2 Diff_eq_empty_iff Set.is_empty_def inf_le2)
        then show "restrict A z \<in> X" by (simp add: calculation)
      qed
      moreover have "\<And>A X. (A, X)\<in>Q_neg - Qn \<Longrightarrow> restrict A z \<notin> X"
      proof -
        fix A X assume "(A, X) \<in> Q_neg - Qn"
        then have notc: "\<not> (card A \<ge> 1 \<and> A \<subseteq> V)" using Qn_def by auto
        then show "restrict A z \<notin> X"
        proof (cases "A \<subseteq> V")
          case True
          then have "card A = 0" using Qn_def using notc by linarith
          then have "Set.is_empty X"
            by (metis DiffD1 Set.is_empty_def True \<open>(A, X) \<in> Q_neg - Qn\<close> \<open>1 \<le> card V\<close> card_eq_0_iff forall notc prod.simps(2) rev_finite_subset)
          then show ?thesis by (simp add: Set.is_empty_def)
        next
          case False
          then obtain i where "i \<in> A" "i \<notin> V" by blast
          then have "i < n"
          proof -
            have "(A, X) \<in> Q_neg" using \<open>(A, X) \<in> Q_neg - Qn\<close> by auto
            then have "wf_set n A" using assms(2) by auto
            then show ?thesis by (simp add: \<open>i \<in> A\<close> wf_set_def)
          qed
          moreover have "table n A X"
          proof -
            have "(A, X) \<in> Q_neg" using \<open>(A, X) \<in> Q_neg - Qn\<close> by auto
            then show ?thesis using assms(2) by auto
          qed
          have "wf_tuple n V z"
            using \<open>(z \<in> genericJoin V Q Qn) = (wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X))\<close> \<open>z \<in> genericJoin V Q Qn\<close> by blast
          show ?thesis
          proof (rule ccontr)
            let ?zz = "restrict A z"
            assume "\<not> ?zz \<notin> X"
            then have "?zz \<in> X" by blast
            then have "wf_tuple n A ?zz" using \<open>table n A X\<close> table_def by blast
            then have "?zz ! i \<noteq> None"
              by (simp add: \<open>i \<in> A\<close> calculation wf_tuple_def)
            moreover have "z ! i = None" using \<open>wf_tuple n V z\<close> \<open>i \<notin> V\<close> wf_tuple_def using \<open>i < n\<close> by blast
            ultimately show "False"
              using \<open>i < n\<close> \<open>i \<in> A\<close> \<open>wf_tuple n A (restrict A z)\<close> nth_restrict wf_tuple_length by fastforce
          qed
        qed
      qed
      ultimately show ?thesis by blast
    qed
    ultimately have "z \<in> genericJoin V Q Qn \<longleftrightarrow> (\<forall>(A, X)\<in>Q_pos - Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg - Qn. restrict A z \<notin> X)
\<and> wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X)" by blast
    moreover have "V = (\<Union>(A, X)\<in>Q_pos. A)"
    proof -
      have "(\<Union>(A, X)\<in>Q_pos - Q. A) = {}"
      proof -
        have "\<And>A X. (A, X) \<in> (Q_pos - Q) \<Longrightarrow> A = {}" by (simp add: Q_def Set.is_empty_def)
        then show ?thesis by blast
      qed
      moreover have "V = (\<Union>(A, X)\<in>Q. A)" using V_def by simp
      moreover have "(\<Union>(A, X)\<in>Q_pos. A) = (\<Union>(A, X)\<in>Q. A) \<union> (\<Union>(A, X)\<in>Q_pos - Q. A)" using Q_def by auto
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis (is "?a = ?b")
    proof -
      have "?a \<Longrightarrow> ?b" using Diff_iff \<open>(z \<in> genericJoin V Q Qn) = ((\<forall>(A, X)\<in>Q_pos - Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Q_neg - Qn. restrict A z \<notin> X) \<and> wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X))\<close> \<open>V = (\<Union>(A, X)\<in>Q_pos. A)\<close> \<open>wrapperGenericJoin Q_pos Q_neg = genericJoin V Q Qn\<close> by blast
      moreover have "?b \<Longrightarrow> ?a" using Q_def Qn_def \<open>(z \<in> genericJoin V Q Qn) = (wf_tuple n V z \<and> (\<forall>(A, X)\<in>Q. restrict A z \<in> X) \<and> (\<forall>(A, X)\<in>Qn. restrict A z \<notin> X))\<close> \<open>V = (\<Union>(A, X)\<in>Q_pos. A)\<close> \<open>wrapperGenericJoin Q_pos Q_neg = genericJoin V Q Qn\<close> by auto
      ultimately show ?thesis by blast
    qed
  qed
qed

end

end
