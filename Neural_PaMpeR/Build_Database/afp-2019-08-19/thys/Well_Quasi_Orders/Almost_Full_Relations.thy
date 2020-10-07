(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>Almost-Full Relations\<close>

theory Almost_Full_Relations
imports Minimal_Bad_Sequences
begin

lemma (in mbs) mbs':
  assumes "\<not> almost_full_on P A"
  shows "\<exists>m \<in> BAD P. \<forall>g. (m, g) \<in> gseq \<longrightarrow> good P g"
using assms and mbs unfolding almost_full_on_def by blast

(*TODO: move to Option.thy of Isabelle/HOL?*)
subsection \<open>Adding a Bottom Element to a Set\<close>

definition with_bot :: "'a set \<Rightarrow> 'a option set" ("_\<^sub>\<bottom>" [1000] 1000)
where
  "A\<^sub>\<bottom> = {None} \<union> Some ` A"

lemma with_bot_iff [iff]:
  "Some x \<in> A\<^sub>\<bottom> \<longleftrightarrow> x \<in> A"
  by (auto simp: with_bot_def)

lemma NoneI [simp, intro]:
  "None \<in> A\<^sub>\<bottom>"
  by (simp add: with_bot_def)

lemma not_None_the_mem [simp]:
  "x \<noteq> None \<Longrightarrow> the x \<in> A \<longleftrightarrow> x \<in> A\<^sub>\<bottom>"
  by auto

lemma with_bot_cases:
  "u \<in> A\<^sub>\<bottom> \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> u = Some x \<Longrightarrow> P) \<Longrightarrow> (u = None \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma with_bot_empty_conv [iff]:
  "A\<^sub>\<bottom> = {None} \<longleftrightarrow> A = {}"
  by (auto elim: with_bot_cases)

lemma with_bot_UNIV [simp]:
  "UNIV\<^sub>\<bottom> = UNIV"
proof (rule set_eqI)
  fix x :: "'a option"
  show "x \<in> UNIV\<^sub>\<bottom> \<longleftrightarrow> x \<in> UNIV" by (cases x) auto
qed


subsection \<open>Adding a Bottom Element to an Almost-Full Set\<close>

fun
  option_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> bool"
where
  "option_le P None y = True" |
  "option_le P (Some x) None = False" |
  "option_le P (Some x) (Some y) = P x y"

lemma None_imp_good_option_le [simp]:
  assumes "f i = None"
  shows "good (option_le P) f"
  by (rule goodI [of i "Suc i"]) (auto simp: assms)

lemma almost_full_on_with_bot:
  assumes "almost_full_on P A"
  shows "almost_full_on (option_le P) A\<^sub>\<bottom>" (is "almost_full_on ?P ?A")
proof
  fix f :: "nat \<Rightarrow> 'a option"
  assume *: "\<forall>i. f i \<in> ?A"
  show "good ?P f"
  proof (cases "\<forall>i. f i \<noteq> None")
    case True
    then have **: "\<And>i. Some (the (f i)) = f i"
      and "\<And>i. the (f i) \<in> A" using * by auto
    with almost_full_onD [OF assms, of "the \<circ> f"] obtain i j where "i < j"
      and "P (the (f i)) (the (f j))" by auto
    then have "?P (Some (the (f i))) (Some (the (f j)))" by simp
    then have "?P (f i) (f j)" unfolding ** .
    with \<open>i < j\<close> show "good ?P f" by (auto simp: good_def)
  qed auto
qed


subsection \<open>Disjoint Union of Almost-Full Sets\<close>

fun
  sum_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool"
where
  "sum_le P Q (Inl x) (Inl y) = P x y" |
  "sum_le P Q (Inr x) (Inr y) = Q x y" |
  "sum_le P Q x y = False"

lemma not_sum_le_cases:
  assumes "\<not> sum_le P Q a b"
    and "\<And>x y. \<lbrakk>a = Inl x; b = Inl y; \<not> P x y\<rbrakk> \<Longrightarrow> thesis"
    and "\<And>x y. \<lbrakk>a = Inr x; b = Inr y; \<not> Q x y\<rbrakk> \<Longrightarrow> thesis"
    and "\<And>x y. \<lbrakk>a = Inl x; b = Inr y\<rbrakk> \<Longrightarrow> thesis"
    and "\<And>x y. \<lbrakk>a = Inr x; b = Inl y\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
  using assms by (cases a b rule: sum.exhaust [case_product sum.exhaust]) auto

text \<open>
  When two sets are almost-full, then their disjoint sum is almost-full.
\<close>
lemma almost_full_on_Plus:
  assumes "almost_full_on P A" and "almost_full_on Q B"
  shows "almost_full_on (sum_le P Q) (A <+> B)" (is "almost_full_on ?P ?A")
proof
  fix f :: "nat \<Rightarrow> ('a + 'b)"
  let ?I = "f -` Inl ` A"
  let ?J = "f -` Inr ` B"
  assume "\<forall>i. f i \<in> ?A"
  then have *: "?J = (UNIV::nat set) - ?I" by (fastforce)
  show "good ?P f"
  proof (rule ccontr)
    assume bad: "bad ?P f"
    show False
    proof (cases "finite ?I")
      assume "finite ?I"
      then have "infinite ?J" by (auto simp: *)
      then interpret infinitely_many1 "\<lambda>i. f i \<in> Inr ` B"
        by (unfold_locales) (simp add: infinite_nat_iff_unbounded)
      have [dest]: "\<And>i x. f (enum i) = Inl x \<Longrightarrow> False"
        using enum_P by (auto simp: image_iff) (metis Inr_Inl_False)
      let ?f = "\<lambda>i. projr (f (enum i))"
      have B: "\<And>i. ?f i \<in> B" using enum_P by (auto simp: image_iff) (metis sum.sel(2))
      { fix i j :: nat
        assume "i < j"
        then have "enum i < enum j" using enum_less by auto
        with bad have "\<not> ?P (f (enum i)) (f (enum j))" by (auto simp: good_def)
        then have "\<not> Q (?f i) (?f j)" by (auto elim: not_sum_le_cases) }
      then have "bad Q ?f" by (auto simp: good_def)
      moreover from \<open>almost_full_on Q B\<close> and B
        have "good Q ?f" by (auto simp: good_def almost_full_on_def)
      ultimately show False by blast
    next
      assume "infinite ?I"
      then interpret infinitely_many1 "\<lambda>i. f i \<in> Inl ` A"
        by (unfold_locales) (simp add: infinite_nat_iff_unbounded)
      have [dest]: "\<And>i x. f (enum i) = Inr x \<Longrightarrow> False"
        using enum_P by (auto simp: image_iff) (metis Inr_Inl_False)
      let ?f = "\<lambda>i. projl (f (enum i))"
      have A: "\<forall>i. ?f i \<in> A" using enum_P by (auto simp: image_iff) (metis sum.sel(1))
      { fix i j :: nat
        assume "i < j"
        then have "enum i < enum j" using enum_less by auto
        with bad have "\<not> ?P (f (enum i)) (f (enum j))" by (auto simp: good_def)
        then have "\<not> P (?f i) (?f j)" by (auto elim: not_sum_le_cases) }
      then have "bad P ?f" by (auto simp: good_def)
      moreover from \<open>almost_full_on P A\<close> and A
        have "good P ?f" by (auto simp: good_def almost_full_on_def)
      ultimately show False by blast
    qed
  qed
qed


subsection \<open>Dickson's Lemma for Almost-Full Relations\<close>

text \<open>
  When two sets are almost-full, then their Cartesian product is almost-full.
\<close>

definition
  prod_le :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
where
  "prod_le P1 P2 = (\<lambda>(p1, p2) (q1, q2). P1 p1 q1 \<and> P2 p2 q2)"

lemma prod_le_True [simp]:
  "prod_le P (\<lambda>_ _. True) a b = P (fst a) (fst b)"
  by (auto simp: prod_le_def)

lemma almost_full_on_Sigma:
  assumes "almost_full_on P1 A1" and "almost_full_on P2 A2"
  shows "almost_full_on (prod_le P1 P2) (A1 \<times> A2)" (is "almost_full_on ?P ?A")
proof (rule ccontr)
  assume "\<not> almost_full_on ?P ?A"
  then obtain f where f: "\<forall>i. f i \<in> ?A"
    and bad: "bad ?P f" by (auto simp: almost_full_on_def)
  let ?W = "\<lambda>x y. P1 (fst x) (fst y)"
  let ?B = "\<lambda>x y. P2 (snd x) (snd y)"
  from f have fst: "\<forall>i. fst (f i) \<in> A1" and snd: "\<forall>i. snd (f i) \<in> A2"
    by (metis SigmaE fst_conv, metis SigmaE snd_conv)
  from almost_full_on_imp_homogeneous_subseq [OF assms(1) fst]
    obtain \<phi> :: "nat \<Rightarrow> nat" where mono: "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j"
    and *: "\<And>i j. i < j \<Longrightarrow> ?W (f (\<phi> i)) (f (\<phi> j))" by auto
  from snd have "\<forall>i. snd (f (\<phi> i)) \<in> A2" by auto
  then have "snd \<circ> f \<circ> \<phi> \<in> SEQ A2" by auto
  with assms(2) have "good P2 (snd \<circ> f \<circ> \<phi>)" by (auto simp: almost_full_on_def)
  then obtain i j :: nat
    where "i < j" and "?B (f (\<phi> i)) (f (\<phi> j))" by auto
  with * [OF \<open>i < j\<close>] have "?P (f (\<phi> i)) (f (\<phi> j))" by (simp add: case_prod_beta prod_le_def)
  with mono [OF \<open>i < j\<close>] and bad show False by auto
qed


subsection \<open>Higman's Lemma for Almost-Full Relations\<close>

lemma almost_full_on_lists:
  assumes "almost_full_on P A"
  shows "almost_full_on (list_emb P) (lists A)" (is "almost_full_on ?P ?A")
proof (rule ccontr)
  interpret mbs ?A .
  assume "\<not> ?thesis"
  from mbs' [OF this] obtain m
    where bad: "m \<in> BAD ?P"
    and min: "\<forall>g. (m, g) \<in> gseq \<longrightarrow> good ?P g" ..
  then have lists: "\<And>i. m i \<in> lists A"
    and ne: "\<And>i. m i \<noteq> []" by auto

  define h t where "h = (\<lambda>i. hd (m i))" and "t = (\<lambda>i. tl (m i))"
  have m: "\<And>i. m i = h i # t i" using ne by (simp add: h_def t_def)
  
  have "\<forall>i. h i \<in> A" using ne_lists [OF ne] and lists by (auto simp add: h_def)
  from almost_full_on_imp_homogeneous_subseq [OF assms this] obtain \<phi> :: "nat \<Rightarrow> nat"
    where less: "\<And>i j. i < j \<Longrightarrow> \<phi> i < \<phi> j"
      and P: "\<forall>i j. i < j \<longrightarrow> P (h (\<phi> i)) (h (\<phi> j))" by blast

  have bad_t: "bad ?P (t \<circ> \<phi>)"
  proof
    assume "good ?P (t \<circ> \<phi>)"
    then obtain i j where "i < j" and "?P (t (\<phi> i)) (t (\<phi> j))" by auto
    moreover with P have "P (h (\<phi> i)) (h (\<phi> j))" by blast
    ultimately have "?P (m (\<phi> i)) (m (\<phi> j))"
      by (subst (1 2) m) (rule list_emb_Cons2, auto)
    with less and \<open>i < j\<close> have "good ?P m" by (auto simp: good_def)
    with bad show False by blast
  qed
  
  define m' where "m' = (\<lambda>i. if i < \<phi> 0 then m i else t (\<phi> (i - \<phi> 0)))"

  have m'_less: "\<And>i. i < \<phi> 0 \<Longrightarrow> m' i = m i" by (simp add: m'_def)
  have m'_geq: "\<And>i. i \<ge> \<phi> 0 \<Longrightarrow> m' i = t (\<phi> (i - \<phi> 0))" by (simp add: m'_def)

  have "\<forall>i. m' i \<in> lists A" using ne_lists [OF ne] and lists by (auto simp: m'_def t_def)
  moreover have "length (m' (\<phi> 0)) < length (m (\<phi> 0))" using ne by (simp add: t_def m'_geq)
  moreover have "\<forall>j<\<phi> 0. m' j = m j" by (auto simp: m'_less)
  ultimately have "(m, m') \<in> gseq" using lists by (auto simp: gseq_def)
  moreover have "bad ?P m'"
  proof
    assume "good ?P m'"
    then obtain i j where "i < j" and emb: "?P (m' i) (m' j)" by (auto simp: good_def)
    { assume "j < \<phi> 0"
      with \<open>i < j\<close> and emb have "?P (m i) (m j)" by (auto simp: m'_less)
      with \<open>i < j\<close> and bad have False by blast }
    moreover
    { assume "\<phi> 0 \<le> i"
      with \<open>i < j\<close> and emb have "?P (t (\<phi> (i - \<phi> 0))) (t (\<phi> (j - \<phi> 0)))"
        and "i - \<phi> 0 < j - \<phi> 0" by (auto simp: m'_geq)
      with bad_t have False by auto }
    moreover
    { assume "i < \<phi> 0" and "\<phi> 0 \<le> j"
      with \<open>i < j\<close> and emb have "?P (m i) (t (\<phi> (j - \<phi> 0)))" by (simp add: m'_less m'_geq)
      from list_emb_Cons [OF this, of "h (\<phi> (j - \<phi> 0))"]
        have "?P (m i) (m (\<phi> (j - \<phi> 0)))" using ne by (simp add: h_def t_def)
      moreover have "i < \<phi> (j - \<phi> 0)"
        using less [of 0 "j - \<phi> 0"] and \<open>i < \<phi> 0\<close> and \<open>\<phi> 0 \<le> j\<close>
        by (cases "j = \<phi> 0") auto
      ultimately have False using bad by blast }
    ultimately show False using \<open>i < j\<close> by arith
  qed
  ultimately show False using min by blast
qed


subsection \<open>Natural Numbers\<close>

lemma almost_full_on_UNIV_nat:
  "almost_full_on (\<le>) (UNIV :: nat set)"
proof -
  let ?P = "subseq :: bool list \<Rightarrow> bool list \<Rightarrow> bool"
  have *: "length ` (UNIV :: bool list set) = (UNIV :: nat set)"
    by (metis Ex_list_of_length surj_def)
  have "almost_full_on (\<le>) (length ` (UNIV :: bool list set))"
  proof (rule almost_full_on_hom)
    fix xs ys :: "bool list"
    assume "?P xs ys"
    then show "length xs \<le> length ys"
      by (metis list_emb_length)
  next
    have "finite (UNIV :: bool set)" by auto
    from almost_full_on_lists [OF eq_almost_full_on_finite_set [OF this]]
      show "almost_full_on ?P UNIV" unfolding lists_UNIV .
  qed
  then show ?thesis unfolding * .
qed

end
