(* Author: Alexander Maletzky *)

section \<open>Degree Sections of Power-Products\<close>

theory Degree_Section
  imports Polynomials.MPoly_PM
begin

definition deg_sect :: "'x set \<Rightarrow> nat \<Rightarrow> ('x::countable \<Rightarrow>\<^sub>0 nat) set"
  where "deg_sect X d = .[X] \<inter> {t. deg_pm t = d}"

definition deg_le_sect :: "'x set \<Rightarrow> nat \<Rightarrow> ('x::countable \<Rightarrow>\<^sub>0 nat) set"
  where "deg_le_sect X d = (\<Union>d0\<le>d. deg_sect X d0)"

lemma deg_sectI: "t \<in> .[X] \<Longrightarrow> deg_pm t = d \<Longrightarrow> t \<in> deg_sect X d"
  by (simp add: deg_sect_def)

lemma deg_sectD:
  assumes "t \<in> deg_sect X d"
  shows "t \<in> .[X]" and "deg_pm t = d"
  using assms by (simp_all add: deg_sect_def)

lemma deg_le_sect_alt: "deg_le_sect X d = .[X] \<inter> {t. deg_pm t \<le> d}"
  by (auto simp: deg_le_sect_def deg_sect_def)

lemma deg_le_sectI: "t \<in> .[X] \<Longrightarrow> deg_pm t \<le> d \<Longrightarrow> t \<in> deg_le_sect X d"
  by (simp add: deg_le_sect_alt)

lemma deg_le_sectD:
  assumes "t \<in> deg_le_sect X d"
  shows "t \<in> .[X]" and "deg_pm t \<le> d"
  using assms by (simp_all add: deg_le_sect_alt)

lemma deg_sect_zero [simp]: "deg_sect X 0 = {0}"
  by (auto simp: deg_sect_def zero_in_PPs)

lemma deg_sect_empty: "deg_sect {} d = (if d = 0 then {0} else {})"
  by (auto simp: deg_sect_def)

lemma deg_sect_singleton [simp]: "deg_sect {x} d = {Poly_Mapping.single x d}"
  by (auto simp: deg_sect_def deg_pm_single PPs_singleton)

lemma deg_le_sect_zero [simp]: "deg_le_sect X 0 = {0}"
  by (auto simp: deg_le_sect_def)

lemma deg_le_sect_empty [simp]: "deg_le_sect {} d = {0}"
  by (auto simp: deg_le_sect_alt varnum_eq_zero_iff)

lemma deg_le_sect_singleton: "deg_le_sect {x} d = Poly_Mapping.single x ` {..d}"
  by (auto simp: deg_le_sect_alt deg_pm_single PPs_singleton)

lemma deg_sect_mono: "X \<subseteq> Y \<Longrightarrow> deg_sect X d \<subseteq> deg_sect Y d"
  by (auto simp: deg_sect_def dest: PPs_mono)

lemma deg_le_sect_mono_1: "X \<subseteq> Y \<Longrightarrow> deg_le_sect X d \<subseteq> deg_le_sect Y d"
  by (auto simp: deg_le_sect_alt dest: PPs_mono)

lemma deg_le_sect_mono_2: "d1 \<le> d2 \<Longrightarrow> deg_le_sect X d1 \<subseteq> deg_le_sect X d2"
  by (auto simp: deg_le_sect_alt)

lemma zero_in_deg_le_sect: "0 \<in> deg_le_sect n d"
  by (simp add: deg_le_sect_alt zero_in_PPs)

lemma deg_sect_disjoint: "d1 \<noteq> d2 \<Longrightarrow> deg_sect X d1 \<inter> deg_sect Y d2 = {}"
  by (auto simp: deg_sect_def)

lemma deg_le_sect_deg_sect_disjoint: "d1 < d2 \<Longrightarrow> deg_le_sect Y d1 \<inter> deg_sect X d2 = {}"
  by (auto simp: deg_sect_def deg_le_sect_alt)

lemma deg_sect_Suc:
  "deg_sect X (Suc d) = (\<Union>x\<in>X. (+) (Poly_Mapping.single x 1) ` deg_sect X d)" (is "?A = ?B")
proof (rule set_eqI)
  fix t
  show "t \<in> ?A \<longleftrightarrow> t \<in> ?B"
  proof
    assume "t \<in> ?A"
    hence "t \<in> .[X]" and "deg_pm t = Suc d" by (rule deg_sectD)+
    from this(2) have "keys t \<noteq> {}" by auto
    then obtain x where "x \<in> keys t" by blast
    hence "1 \<le> lookup t x" by (simp add: in_keys_iff)
    from \<open>t \<in> .[X]\<close> have "keys t \<subseteq> X" by (rule PPsD)
    with \<open>x \<in> keys t\<close> have "x \<in> X" ..
    let ?s = "Poly_Mapping.single x (1::nat)"
    from \<open>1 \<le> lookup t x\<close> have "?s adds t"
      by (auto simp: lookup_single when_def intro!: adds_poly_mappingI le_funI)
    hence t: "?s + (t - ?s) = t" by (metis add.commute adds_minus)
    have "t - ?s \<in> deg_sect X d"
    proof (rule deg_sectI)
      from \<open>t \<in> .[X]\<close> show "t - ?s \<in> .[X]" by (rule PPs_closed_minus)
    next
      from deg_pm_plus[of ?s "t - ?s"] have "deg_pm t = Suc (deg_pm (t - ?s))"
        by (simp only: t deg_pm_single)
      thus "deg_pm (t - ?s) = d" by (simp add: \<open>deg_pm t = Suc d\<close>)
    qed
    hence "?s + (t - ?s) \<in> (+) ?s ` deg_sect X d" by (rule imageI)
    hence "t \<in> (+) ?s ` deg_sect X d" by (simp only: t)
    with \<open>x \<in> X\<close> show "t \<in> ?B" ..
  next
    assume "t \<in> ?B"
    then obtain x where "x \<in> X" and "t \<in> (+) (Poly_Mapping.single x 1) ` deg_sect X d" ..
    from this(2) obtain s where s: "s \<in> deg_sect X d"
      and t: "t = Poly_Mapping.single x 1 + s" (is "t = ?s + s") ..
    show "t \<in> ?A"
    proof (rule deg_sectI)
      from \<open>x \<in> X\<close> have "?s \<in> .[X]" by (rule PPs_closed_single)
      moreover from s have "s \<in> .[X]" by (rule deg_sectD)
      ultimately show "t \<in> .[X]" unfolding t by (rule PPs_closed_plus)
    next
      from s have "deg_pm s = d" by (rule deg_sectD)
      thus "deg_pm t = Suc d" by (simp add: t deg_pm_single deg_pm_plus)
    qed
  qed
qed

lemma deg_sect_insert:
  "deg_sect (insert x X) d = (\<Union>d0\<le>d. (+) (Poly_Mapping.single x (d - d0)) ` deg_sect X d0)"
    (is "?A = ?B")
proof (rule set_eqI)
  fix t
  show "t \<in> ?A \<longleftrightarrow> t \<in> ?B"
  proof
    assume "t \<in> ?A"
    hence "t \<in> .[insert x X]" and "deg_pm t = d" by (rule deg_sectD)+
    from this(1) obtain e tx where "tx \<in> .[X]" and t: "t = Poly_Mapping.single x e + tx"
      by (rule PPs_insertE)
    have "e + deg_pm tx = deg_pm t" by (simp add: t deg_pm_plus deg_pm_single)
    hence "e + deg_pm tx = d" by (simp only: \<open>deg_pm t = d\<close>)
    hence "deg_pm tx \<in> {..d}" and e: "e = d - deg_pm tx" by simp_all
    from \<open>tx \<in> .[X]\<close> refl have "tx \<in> deg_sect X (deg_pm tx)" by (rule deg_sectI)
    hence "t \<in> (+) (Poly_Mapping.single x (d - deg_pm tx)) ` deg_sect X (deg_pm tx)"
      unfolding t e by (rule imageI)
    with \<open>deg_pm tx \<in> {..d}\<close> show "t \<in> ?B" ..
  next
    assume "t \<in> ?B"
    then obtain d0 where "d0 \<in> {..d}" and "t \<in> (+) (Poly_Mapping.single x (d - d0)) ` deg_sect X d0" ..
    from this(2) obtain s where s: "s \<in> deg_sect X d0"
      and t: "t = Poly_Mapping.single x (d - d0) + s" (is "t = ?s + s") ..
    show "t \<in> ?A"
    proof (rule deg_sectI)
      have "?s \<in> .[insert x X]" by (rule PPs_closed_single, simp)
      from s have "s \<in> .[X]" by (rule deg_sectD)
      also have "... \<subseteq> .[insert x X]" by (rule PPs_mono, blast)
      finally have "s \<in> .[insert x X]" .
      with \<open>?s \<in> .[insert x X]\<close> show "t \<in> .[insert x X]" unfolding t by (rule PPs_closed_plus)
    next
      from s have "deg_pm s = d0" by (rule deg_sectD)
      moreover from \<open>d0 \<in> {..d}\<close> have "d0 \<le> d" by simp
      ultimately show "deg_pm t = d" by (simp add: t deg_pm_single deg_pm_plus)
    qed
  qed
qed

lemma deg_le_sect_Suc: "deg_le_sect X (Suc d) = deg_le_sect X d \<union> deg_sect X (Suc d)"
  by (simp add: deg_le_sect_def atMost_Suc Un_commute)

lemma deg_le_sect_Suc_2:
  "deg_le_sect X (Suc d) = insert 0 (\<Union>x\<in>X. (+) (Poly_Mapping.single x 1) ` deg_le_sect X d)"
    (is "?A = ?B")
proof -
  have eq1: "{Suc 0..Suc d} = Suc ` {..d}" by (simp add: image_Suc_atMost)
  have "insert 0 {1..Suc d} = {..Suc d}" by fastforce
  hence "?A = (\<Union>d0\<in>insert 0 {1..Suc d}. deg_sect X d0)" by (simp add: deg_le_sect_def)
  also have "... = insert 0 (\<Union>d0\<le>d. deg_sect X (Suc d0))" by (simp add: eq1)
  also have "... = insert 0 (\<Union>d0\<le>d. (\<Union>x\<in>X. (+) (Poly_Mapping.single x 1) ` deg_sect X d0))"
    by (simp only: deg_sect_Suc)
  also have "... = insert 0 (\<Union>x\<in>X. (+) (Poly_Mapping.single x 1) ` (\<Union>d0\<le>d. deg_sect X d0))"
    by fastforce
  also have "... = ?B" by (simp only: deg_le_sect_def)
  finally show ?thesis .
qed

lemma finite_deg_sect:
  assumes "finite X"
  shows "finite ((deg_sect X d)::('x::countable \<Rightarrow>\<^sub>0 nat) set)"
proof (induct d)
  case 0
  show ?case by simp
next
  case (Suc d)
  with assms show ?case by (simp add: deg_sect_Suc)
qed

corollary finite_deg_le_sect: "finite X \<Longrightarrow> finite ((deg_le_sect X d)::('x::countable \<Rightarrow>\<^sub>0 nat) set)"
  by (simp add: deg_le_sect_def finite_deg_sect)

lemma keys_subset_deg_le_sectI:
  assumes "p \<in> P[X]" and "poly_deg p \<le> d"
  shows "keys p \<subseteq> deg_le_sect X d"
proof
  fix t
  assume "t \<in> keys p"
  also from assms(1) have "... \<subseteq> .[X]" by (rule PolysD)
  finally have "t \<in> .[X]" .
  from \<open>t \<in> keys p\<close> have "deg_pm t \<le> poly_deg p" by (rule poly_deg_max_keys)
  from this assms(2) have "deg_pm t \<le> d" by (rule le_trans)
  with \<open>t \<in> .[X]\<close> show "t \<in> deg_le_sect X d" by (rule deg_le_sectI)
qed

lemma binomial_symmetric_plus: "(n + k) choose n = (n + k) choose k"
  by (metis add_diff_cancel_left' binomial_symmetric le_add1)

lemma card_deg_sect:
  assumes "finite X" and "X \<noteq> {}"
  shows "card (deg_sect X d) = (d + (card X - 1)) choose (card X - 1)"
  using assms
proof (induct X arbitrary: d)
  case empty
  thus ?case by simp
next
  case (insert x X)
  from insert(1, 2) have eq1: "card (insert x X) = Suc (card X)" by simp
  show ?case
  proof (cases "X = {}")
    case True
    thus ?thesis by simp
  next
    case False
    with insert.hyps(1) have "0 < card X" by (simp add: card_gt_0_iff)
    let ?f = "\<lambda>d0. Poly_Mapping.single x (d - d0)"
    from False have eq2: "card (deg_sect X d0) = d0 + (card X - 1) choose (card X - 1)" for d0
      by (rule insert.hyps)
    have "finite {..d}" by simp
    moreover from insert.hyps(1) have "\<forall>d0\<in>{..d}. finite ((+) (?f d0) ` deg_sect X d0)"
      by (simp add: finite_deg_sect)
    moreover have "\<forall>d0\<in>{..d}. \<forall>d1\<in>{..d}. d0 \<noteq> d1 \<longrightarrow>
                          ((+) (?f d0) ` deg_sect X d0) \<inter> ((+) (?f d1) ` deg_sect X d1) = {}"
    proof (intro ballI impI, rule ccontr)
      fix d1 d2 :: nat
      assume "d1 \<noteq> d2"
      assume "((+) (?f d1) ` deg_sect X d1) \<inter> ((+) (?f d2) ` deg_sect X d2) \<noteq> {}"
      then obtain t where "t \<in> ((+) (?f d1) ` deg_sect X d1) \<inter> ((+) (?f d2) ` deg_sect X d2)"
        by blast
      hence t1: "t \<in> (+) (?f d1) ` deg_sect X d1" and t2: "t \<in> (+) (?f d2) ` deg_sect X d2" by simp_all
      from t1 obtain s1 where "s1 \<in> deg_sect X d1" and s1: "t = ?f d1 + s1" ..
      from this(1) have "s1 \<in> .[X]" by (rule deg_sectD)
      hence "keys s1 \<subseteq> X" by (rule PPsD)
      with insert.hyps(2) have eq3: "lookup s1 x = 0" by (auto simp: in_keys_iff)
      from t2 obtain s2 where "s2 \<in> deg_sect X d2" and s2: "t = ?f d2 + s2" ..
      from this(1) have "s2 \<in> .[X]" by (rule deg_sectD)
      hence "keys s2 \<subseteq> X" by (rule PPsD)
      with insert.hyps(2) have eq4: "lookup s2 x = 0" by (auto simp: in_keys_iff)
      from s2 have "lookup (?f d1 + s1) x = lookup (?f d2 + s2) x" by (simp only: s1)
      hence "d - d1 = d - d2" by (simp add: lookup_add eq3 eq4)
      moreover assume "d1 \<in> {..d}" and "d2 \<in> {..d}"
      ultimately have "d1 = d2" by simp
      with \<open>d1 \<noteq> d2\<close> show False ..
    qed
    ultimately have "card (deg_sect (insert x X) d) =
                       (\<Sum>d0\<le>d. card ((+) (monomial (d - d0) x) ` deg_sect X d0))"
      unfolding deg_sect_insert by (rule card_UN_disjoint)
    also from refl have "... = (\<Sum>d0\<le>d. card (deg_sect X d0))"
    proof (rule sum.cong)
      fix d0
      have "inj_on ((+) (monomial (d - d0) x)) (deg_sect X d0)" by (rule, rule add_left_imp_eq)
      thus "card ((+) (monomial (d - d0) x) ` deg_sect X d0) = card (deg_sect X d0)"
        by (rule card_image)
    qed
    also have "... = (\<Sum>d0\<le>d. (card X - 1) + d0 choose (card X - 1))" by (simp only: eq2 add.commute)
    also have "... = (\<Sum>d0\<le>d. (card X - 1) + d0 choose d0)" by (simp only: binomial_symmetric_plus)
    also have "... = Suc ((card X - 1) + d) choose d" by (rule sum_choose_lower)
    also from \<open>0 < card X\<close> have "... = d + (card (insert x X) - 1) choose d"
      by (simp add: eq1 add.commute)
    also have "... = d + (card (insert x X) - 1) choose (card (insert x X) - 1)"
      by (fact binomial_symmetric_plus)
    finally show ?thesis .
  qed
qed

corollary card_deg_sect_Suc:
  assumes "finite X"
  shows "card (deg_sect X (Suc d)) = (d + card X) choose (Suc d)"
proof (cases "X = {}")
  case True
  thus ?thesis by (simp add: deg_sect_empty)
next
  case False
  with assms have "0 < card X" by (simp add: card_gt_0_iff)
  from assms False have "card (deg_sect X (Suc d)) = (Suc d + (card X - 1)) choose (card X - 1)"
    by (rule card_deg_sect)
  also have "... = (Suc d + (card X - 1)) choose (Suc d)" by (rule sym, rule binomial_symmetric_plus)
  also from \<open>0 < card X\<close> have "... = (d + card X) choose (Suc d)" by simp
  finally show ?thesis .
qed

corollary card_deg_le_sect:
  assumes "finite X"
  shows "card (deg_le_sect X d) = (d + card X) choose card X"
proof (induct d)
  case 0
  show ?case by simp
next
  case (Suc d)
  from assms have "finite (deg_le_sect X d)" by (rule finite_deg_le_sect)
  moreover from assms have "finite (deg_sect X (Suc d))" by (rule finite_deg_sect)
  moreover from lessI have "deg_le_sect X d \<inter> deg_sect X (Suc d) = {}"
    by (rule deg_le_sect_deg_sect_disjoint)
  ultimately have "card (deg_le_sect X (Suc d)) = card (deg_le_sect X d) + card (deg_sect X (Suc d))"
    unfolding deg_le_sect_Suc by (rule card_Un_disjoint)
  also from assms have "... = (Suc d + card X) choose Suc d"
    by (simp add: Suc.hyps card_deg_sect_Suc binomial_symmetric_plus[of d])
  also have "... = (Suc d + card X) choose card X" by (rule binomial_symmetric_plus)
  finally show ?case .
qed

end (* theory *)
