(*  Title:       CCPO_Topology.thy
    Author:      Johannes Hölzl, TU Munich
*)

section \<open>CCPO topologies\<close>

theory CCPO_Topology
imports
  "HOL-Analysis.Extended_Real_Limits"
  "../Coinductive_Nat"
begin

lemma dropWhile_append:
  "dropWhile P (xs @ ys) = (if \<forall>x\<in>set xs. P x then dropWhile P ys else dropWhile P xs @ ys)"
  by auto

lemma dropWhile_False: "(\<And>x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow> dropWhile P xs = []"
  by simp

abbreviation (in order) "chain \<equiv> Complete_Partial_Order.chain (\<le>)"

lemma (in linorder) chain_linorder: "chain C"
  by (simp add: chain_def linear)

lemma continuous_add_ereal:
  assumes "0 \<le> t"
  shows "continuous_on {-\<infinity>::ereal <..} (\<lambda>x. t + x)"
proof (subst continuous_on_open_vimage, (intro open_greaterThan allI impI)+)
  fix B :: "ereal set" assume "open B"
  show "open ((\<lambda>x. t + x) -` B \<inter> {- \<infinity><..})"
  proof (cases t)
    case (real t')
    then have *: "(\<lambda>x. t + x) -` B \<inter> {- \<infinity><..} = (\<lambda>x. 1 * x + (-t)) ` (B \<inter> {-\<infinity> <..})"
      apply (simp add: set_eq_iff image_iff Bex_def)
      apply (intro allI iffI)
      apply (rule_tac x= "x + ereal t'" in exI)
      apply (case_tac x)
      apply (auto simp: ac_simps)
      done
    show ?thesis
      unfolding *
      apply (rule ereal_open_affinity_pos)
      using \<open>open B\<close>
      apply (auto simp: real)
      done
  qed (insert \<open>0 \<le> t\<close>, auto)
qed

lemma tendsto_add_ereal:
  "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> (f \<longlongrightarrow> y) F \<Longrightarrow> ((\<lambda>z. x + f z :: ereal) \<longlongrightarrow> x + y) F"
  apply (rule tendsto_compose[where f=f])
  using continuous_add_ereal[where t=x]
  unfolding continuous_on_def
  apply (auto simp add: at_within_open[where S="{- \<infinity> <..}"])
  done

lemma tendsto_LimI: "(f \<longlongrightarrow> y) F \<Longrightarrow> (f \<longlongrightarrow> Lim F f) F"
  by (metis tendsto_Lim tendsto_bot)

subsection \<open>The filter \<open>at'\<close>\<close>

abbreviation (in ccpo) "compact_element \<equiv> ccpo.compact Sup (\<le>)"

lemma tendsto_unique_eventually:
  fixes x x' :: "'a :: t2_space"
  shows "F \<noteq> bot \<Longrightarrow> eventually (\<lambda>x. f x = g x) F \<Longrightarrow> (f \<longlongrightarrow> x) F \<Longrightarrow> (g \<longlongrightarrow> x') F \<Longrightarrow> x = x'"
  by (metis tendsto_unique filterlim_cong)

lemma (in ccpo) ccpo_Sup_upper2: "chain C \<Longrightarrow> x \<in> C \<Longrightarrow> y \<le> x \<Longrightarrow> y \<le> Sup C"
  by (blast intro: ccpo_Sup_upper order_trans)

lemma tendsto_open_vimage: "(\<And>B. open B \<Longrightarrow> open (f -` B)) \<Longrightarrow> f \<midarrow>l\<rightarrow> f l"
  using continuous_on_open_vimage[of UNIV f] continuous_on_def[of UNIV f] by simp

lemma open_vimageI: "(\<And>x. f \<midarrow>x\<rightarrow> f x) \<Longrightarrow> open A \<Longrightarrow> open (f -` A)"
  using continuous_on_open_vimage[of UNIV f] continuous_on_def[of UNIV f] by simp

lemma principal_bot: "principal x = bot \<longleftrightarrow> x = {}"
  by (auto simp: filter_eq_iff eventually_principal)

definition "at' x = (if open {x} then principal {x} else at x)"

lemma at'_bot: "at' x \<noteq> bot"
  by (simp add: at'_def at_eq_bot_iff principal_bot)

lemma tendsto_id_at'[simp, intro]: "((\<lambda>x. x) \<longlongrightarrow> x) (at' x)"
  by (simp add: at'_def topological_tendstoI eventually_principal tendsto_ident_at)

lemma cont_at': "(f \<longlongrightarrow> f x) (at' x) \<longleftrightarrow> f \<midarrow>x\<rightarrow> f x"
  using at_eq_bot_iff[of x] by (auto split: if_split_asm intro!: topological_tendstoI simp: eventually_principal at'_def)

subsection \<open>The type class \<open>ccpo_topology\<close>\<close>

text \<open>Temporarily relax type constraints for @{term "open"}.\<close>
setup \<open>Sign.add_const_constraint
  (@{const_name "open"}, SOME @{typ "'a::open set \<Rightarrow> bool"})\<close>

class ccpo_topology = "open" + ccpo +
  assumes open_ccpo: "open A \<longleftrightarrow> (\<forall>C. chain C \<longrightarrow> C \<noteq> {} \<longrightarrow> Sup C \<in> A \<longrightarrow> C \<inter> A \<noteq> {})"
begin

lemma open_ccpoD:
  assumes "open A" "chain C" "C \<noteq> {}" "Sup C \<in> A"
  shows "\<exists>c\<in>C. \<forall>c'\<in>C. c \<le> c' \<longrightarrow> c' \<in> A"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have *: "\<And>c. c \<in> C \<Longrightarrow> \<exists>c'\<in>C. c \<le> c' \<and> c' \<notin> A"
    by auto
  with \<open>chain C\<close> \<open>C \<noteq> {}\<close> have "chain (C - A)" "C - A \<noteq> {}"
    by (auto intro: chain_Diff)
  moreover have "Sup C = Sup (C - A)"
  proof (safe intro!: antisym ccpo_Sup_least \<open>chain C\<close> chain_Diff)
    fix c assume "c \<in> C"
    with * obtain c' where "c' \<in> C" "c \<le> c'" "c' \<notin> A"
      by auto
    with \<open>c\<in>C\<close> show "c \<le> \<Squnion>(C - A)"
      by (intro ccpo_Sup_upper2 \<open>chain (C - A)\<close>) auto
  qed (auto intro: \<open>chain C\<close> ccpo_Sup_upper)
  ultimately show False
    using \<open>open A\<close> \<open>Sup C \<in> A\<close> by (auto simp: open_ccpo)
qed

lemma open_ccpo_Iic: "open {.. b}"
  by (auto simp: open_ccpo) (metis Int_iff atMost_iff ccpo_Sup_upper empty_iff order_trans)

subclass topological_space
proof
  show "open (UNIV::'a set)"
    unfolding open_ccpo by auto
next
  fix S T :: "'a set" assume "open S" "open T"
  show "open (S \<inter> T)"
    unfolding open_ccpo
  proof (intro allI impI)
    fix C assume C: "chain C" "C \<noteq> {}" and "\<Squnion>C \<in> S \<inter> T"
    with open_ccpoD[OF \<open>open S\<close> C] open_ccpoD[OF \<open>open T\<close> C]
    show "C \<inter> (S \<inter> T) \<noteq> {}"
      unfolding chain_def by blast
  qed
next
  fix K :: "'a set set" assume *: "\<forall>D\<in>K. open D"
  show "open (\<Union>K)"
    unfolding open_ccpo
  proof (intro allI impI)
    fix C assume "chain C" "C \<noteq> {}" "\<Squnion>C \<in> (\<Union>K)"
    with * obtain D where "D \<in> K" "\<Squnion>C \<in> D" "C \<inter> D \<noteq> {}"
      by (auto simp: open_ccpo)
    then show "C \<inter> (\<Union>K) \<noteq> {}"
      by auto
  qed
qed

lemma closed_ccpo: "closed A \<longleftrightarrow> (\<forall>C. chain C \<longrightarrow> C \<noteq> {} \<longrightarrow> C \<subseteq> A \<longrightarrow> Sup C \<in> A)"
  unfolding closed_def open_ccpo by auto

lemma closed_admissible: "closed {x. P x} \<longleftrightarrow> ccpo.admissible Sup (\<le>) P"
  unfolding closed_ccpo ccpo.admissible_def by auto

lemma open_singletonI_compact: "compact_element x \<Longrightarrow> open {x}"
  using admissible_compact_neq[of Sup "(\<le>)" x]
  by (simp add: closed_admissible[symmetric] open_closed Collect_neg_eq)

lemma closed_Ici: "closed {.. b}"
  by (auto simp: closed_ccpo intro: ccpo_Sup_least)

lemma closed_Iic: "closed {b ..}"
  by (auto simp: closed_ccpo intro: ccpo_Sup_upper2)

text \<open>
  @{class ccpo_topology}s are also @{class t2_space}s.
  This is necessary to have a unique continuous extension.
\<close>

subclass t2_space
proof
  fix x y :: 'a assume "x \<noteq> y"
  show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
  proof cases
    { fix x y assume "x \<noteq> y" "x \<le> y"
      then have "open {..x} \<and> open (- {..x}) \<and> x \<in> {..x} \<and> y \<in> - {..x} \<and> {..x} \<inter> - {..x} = {}"
        by (auto intro: open_ccpo_Iic closed_Ici) }
    moreover assume "x \<le> y \<or> y \<le> x"
    ultimately show ?thesis
      using \<open>x \<noteq> y\<close> by (metis Int_commute)
  next
    assume "\<not> (x \<le> y \<or> y \<le> x)"
    then have "open ({..x} \<inter> - {..y}) \<and> open ({..y} \<inter> - {..x}) \<and>
        x \<in> {..x} \<inter> - {..y} \<and> y \<in> {..y} \<inter> - {..x} \<and> ({..x} \<inter> - {..y}) \<inter> ({..y} \<inter> - {..x}) = {}"
      by (auto intro: open_ccpo_Iic closed_Ici)
    then show ?thesis by auto
  qed
qed

end

lemma tendsto_le_ccpo:
  fixes f g :: "'a \<Rightarrow> 'b::ccpo_topology"
  assumes F: "\<not> trivial_limit F"
  assumes x: "(f \<longlongrightarrow> x) F" and y: "(g \<longlongrightarrow> y) F"
  assumes ev: "eventually (\<lambda>x. g x \<le> f x) F"
  shows "y \<le> x"
proof (rule ccontr)
  assume "\<not> y \<le> x"

  show False
  proof cases
    assume "x \<le> y"
    with \<open>\<not> y \<le> x\<close>
    have "open {..x}" "open (- {..x})" "x \<in> {..x}" "y \<in> - {..x}" "{..x} \<inter> - {..x} = {}"
      by (auto intro: open_ccpo_Iic closed_Ici)
    with topological_tendstoD[OF x, of "{..x}"] topological_tendstoD[OF y, of "- {..x}"]
    have "eventually (\<lambda>z. f z \<le> x) F" "eventually (\<lambda>z. \<not> g z \<le> x) F"
      by auto
    with ev have "eventually (\<lambda>x. False) F" by eventually_elim (auto intro: order_trans)
    with F show False by (auto simp: eventually_False)
  next
    assume "\<not> x \<le> y"
    with \<open>\<not> y \<le> x\<close> have "open ({..x} \<inter> - {..y})" "open ({..y} \<inter> - {..x})"
        "x \<in> {..x} \<inter> - {..y}" "y \<in> {..y} \<inter> - {..x}" "({..x} \<inter> - {..y}) \<inter> ({..y} \<inter> - {..x}) = {}"
      by (auto intro: open_ccpo_Iic closed_Ici)
    with topological_tendstoD[OF x, of "{..x} \<inter> - {..y}"]
         topological_tendstoD[OF y, of "{..y} \<inter> - {..x}"]
    have "eventually (\<lambda>z. f z \<le> x \<and> \<not> f z \<le> y) F" "eventually (\<lambda>z. g z \<le> y \<and> \<not> g z \<le> x) F"
      by auto
    with ev have "eventually (\<lambda>x. False) F" by eventually_elim (auto intro: order_trans)
    with F show False by (auto simp: eventually_False)
  qed
qed

lemma tendsto_ccpoI:
  fixes f :: "'a::ccpo_topology \<Rightarrow> 'b::ccpo_topology"
  shows "(\<And>C. chain C \<Longrightarrow> C \<noteq> {} \<Longrightarrow> chain (f ` C) \<and> f (Sup C) = Sup (f`C)) \<Longrightarrow> f \<midarrow>x\<rightarrow> f x"
  by (intro tendsto_open_vimage) (auto simp: open_ccpo)

lemma tendsto_mcont:
  assumes mcont: "mcont Sup (\<le>) Sup (\<le>) (f :: 'a :: ccpo_topology \<Rightarrow> 'b :: ccpo_topology)"
  shows "f \<midarrow>l\<rightarrow> f l"
proof (intro tendsto_ccpoI conjI)
  fix C :: "'a set" assume C: "chain C" "C \<noteq> {}"
  show "chain (f`C)"
    using mcont
    by (intro chain_imageI[where le_a="(\<le>)"] C) (simp add: mcont_def monotone_def)
  show "f (\<Squnion>C) = \<Squnion>(f ` C)"
    using mcont C by (simp add: mcont_def cont_def)
qed

subsection \<open>Instances for @{class ccpo_topology}s and continuity theorems\<close>

instantiation set :: (type) ccpo_topology
begin

definition open_set :: "'a set set \<Rightarrow> bool" where
  "open_set A \<longleftrightarrow> (\<forall>C. chain C \<longrightarrow> C \<noteq> {} \<longrightarrow> Sup C \<in> A \<longrightarrow> C \<inter> A \<noteq> {})"

instance
  by intro_classes (simp add: open_set_def)

end

instantiation enat :: ccpo_topology
begin

instance
proof
  fix A :: "enat set"
  show "open A = (\<forall>C. chain C \<longrightarrow> C \<noteq> {} \<longrightarrow> \<Squnion>C \<in> A \<longrightarrow> C \<inter> A \<noteq> {})"
  proof (intro iffI allI impI)
    fix C x assume "open A" "chain C" "C \<noteq> {}" "\<Squnion>C \<in> A"

    show "C \<inter> A \<noteq> {}"
    proof cases
      assume "\<Squnion>C = \<infinity>"
      with \<open>\<Squnion>C \<in> A\<close> \<open>open A\<close> obtain n where "{enat n <..} \<subseteq> A"
        unfolding open_enat_iff by auto
      with \<open>\<Squnion>C = \<infinity>\<close> Sup_eq_top_iff[of C] show ?thesis
        by (auto simp: top_enat_def)
    next
      assume "\<Squnion>C \<noteq> \<infinity>"
      then obtain n where "C \<subseteq> {.. enat n}"
        unfolding Sup_eq_top_iff top_enat_def[symmetric] by (auto simp: not_less top_enat_def)
      moreover have "finite {.. enat n}"
        by (auto intro: finite_enat_bounded)
      ultimately have "finite C"
        by (auto intro: finite_subset)
      from in_chain_finite[OF \<open>chain C\<close> \<open>finite C\<close> \<open>C \<noteq> {}\<close>] \<open>\<Squnion>C \<in> A\<close> show ?thesis
        by auto
    qed
  next
    assume C: "\<forall>C. chain C \<longrightarrow> C \<noteq> {} \<longrightarrow> \<Squnion>C \<in> A \<longrightarrow> C \<inter> A \<noteq> {}"
    show "open A"
      unfolding open_enat_iff
    proof safe
      assume "\<infinity> \<in> A"
      { fix C :: "enat set" assume "infinite C"
        then have "\<Squnion>C = \<infinity>"
          by (auto simp: Sup_enat_def)
        with \<open>infinite C\<close> C[THEN spec, of C] \<open>\<infinity> \<in> A\<close> have "C \<inter> A \<noteq> {}"
          by auto }
      note inf_C = this

      show "\<exists>x. {enat x<..} \<subseteq> A"
      proof (rule ccontr)
        assume "\<not> (\<exists>x. {enat x<..} \<subseteq> A)"
        with \<open>\<infinity> \<in> A\<close> have "\<And>x. \<exists>y>x. enat y \<notin> A"
          by (simp add: subset_eq Bex_def) (metis enat.exhaust enat_ord_simps(2))
        then have "infinite {n. enat n \<notin> A}"
          unfolding infinite_nat_iff_unbounded by auto
        then have "infinite (enat ` {n. enat n \<notin> A})"
          by (auto dest!: finite_imageD)
        from inf_C[OF this] show False
          by auto
      qed
    qed
  qed
qed

end

lemmas tendsto_inf2[THEN tendsto_compose, tendsto_intros] =
  tendsto_mcont[OF mcont_inf2]

lemma isCont_inf2[THEN isCont_o2[rotated]]:
  "isCont (\<lambda>x. x \<sqinter> y) (z :: _ :: {ccpo_topology, complete_distrib_lattice})"
  by(simp add: isCont_def tendsto_inf2 tendsto_ident_at)

lemmas tendsto_sup1[THEN tendsto_compose, tendsto_intros] =
  tendsto_mcont[OF mcont_sup1]

lemma isCont_If: "isCont f x \<Longrightarrow> isCont g x \<Longrightarrow> isCont (\<lambda>x. if Q then f x else g x) x"
  by (cases Q) auto

lemma isCont_enat_case: "isCont (f (epred n)) x \<Longrightarrow> isCont g x \<Longrightarrow> isCont (\<lambda>x. co.case_enat (g x) (\<lambda>n. f n x) n) x"
  by (cases n rule: enat_coexhaust) auto

end
