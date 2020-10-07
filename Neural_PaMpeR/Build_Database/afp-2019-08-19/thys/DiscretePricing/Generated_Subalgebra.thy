(*  Title:      Restricted_Measure_Space.thy
    Author:     Mnacho Echenim, Univ. Grenoble Alpes
*)

section \<open>Generated subalgebras\<close>

text \<open>This section contains definitions and properties related to generated subalgebras.\<close>

theory Generated_Subalgebra imports "HOL-Probability.Probability"

begin



definition gen_subalgebra where
"gen_subalgebra M G = sigma (space M) G"


lemma gen_subalgebra_space:
  shows "space (gen_subalgebra M G) = space M"
by (simp add: gen_subalgebra_def space_measure_of_conv)


lemma gen_subalgebra_sets:
  assumes "G \<subseteq> sets M"
  and "A \<in> G"
  shows "A \<in> sets (gen_subalgebra M G)"
by (metis assms gen_subalgebra_def sets.space_closed sets_measure_of sigma_sets.Basic subset_trans)


lemma gen_subalgebra_sig_sets:
  assumes "G \<subseteq> Pow (space M)"
  shows "sets (gen_subalgebra M G) = sigma_sets (space M) G" unfolding gen_subalgebra_def
by (metis assms gen_subalgebra_def sets_measure_of)

lemma  gen_subalgebra_sigma_sets:
  assumes "G \<subseteq> sets M"
  and "sigma_algebra (space M) G"
  shows "sets (gen_subalgebra M G) = G"
using assms by (simp add: gen_subalgebra_def sigma_algebra.sets_measure_of_eq)


lemma gen_subalgebra_is_subalgebra:
  assumes sub: "G \<subseteq> sets M"
  and sigal:"sigma_algebra (space M) G"
  shows "subalgebra M (gen_subalgebra M G)" (is "subalgebra M ?N")
unfolding subalgebra_def
proof (intro conjI)
  show "space ?N = space M" using space_measure_of_conv[of "(space M)"]  unfolding gen_subalgebra_def by simp
  have geqn: "G = sets ?N" using assms by (simp add:gen_subalgebra_sigma_sets)
  thus "sets ?N \<subseteq> sets M" using assms by simp
qed


definition  fct_gen_subalgebra :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a measure" where
  "fct_gen_subalgebra M N X = gen_subalgebra M (sigma_sets (space M) {X -` B \<inter> (space M) | B. B \<in> sets N})"



lemma fct_gen_subalgebra_sets:
  shows "sets (fct_gen_subalgebra M N X) = sigma_sets (space M) {X -` B \<inter> space M |B. B \<in> sets N}"
unfolding fct_gen_subalgebra_def gen_subalgebra_def
proof -
  have "{X -` B \<inter> space M |B. B \<in> sets N} \<subseteq> Pow (space M)"
    by blast
  then show "sets (sigma (space M) (sigma_sets (space M) {X -` B \<inter> space M |B. B \<in> sets N})) = sigma_sets (space M) {X -` B \<inter> space M |B. B \<in> sets N}"
    by (meson sigma_algebra.sets_measure_of_eq sigma_algebra_sigma_sets)
qed

lemma fct_gen_subalgebra_space:
  shows "space (fct_gen_subalgebra M N X) = space M"
  unfolding fct_gen_subalgebra_def by (simp add: gen_subalgebra_space)

lemma fct_gen_subalgebra_eq_sets:
  assumes "sets M = sets P"
  shows "fct_gen_subalgebra M N X = fct_gen_subalgebra P N X"
proof -
  have "space M = space P" using sets_eq_imp_space_eq assms by auto
  thus ?thesis unfolding fct_gen_subalgebra_def gen_subalgebra_def by simp
qed

lemma fct_gen_subalgebra_sets_mem:
  assumes "B\<in> sets N"
  shows "X -` B \<inter> (space M) \<in> sets (fct_gen_subalgebra M N X)" unfolding fct_gen_subalgebra_def
proof -
  have f1: "{X -` A \<inter> space M |A. A \<in> sets N} \<subseteq> Pow (space M)"
    by blast
  have "\<exists>A. X -` B \<inter> space M = X -` A \<inter> space M \<and> A \<in> sets N"
    by (metis assms)
  then show "X -` B \<inter> space M \<in> sets (gen_subalgebra M (sigma_sets (space M) {X -` A \<inter> space M |A. A \<in> sets N}))"
    using f1 by (simp add: gen_subalgebra_def sigma_algebra.sets_measure_of_eq sigma_algebra_sigma_sets)
qed

lemma fct_gen_subalgebra_is_subalgebra:
  assumes "X\<in> measurable M N"
  shows "subalgebra M (fct_gen_subalgebra M N X)"
unfolding fct_gen_subalgebra_def
proof (rule gen_subalgebra_is_subalgebra)
  show "sigma_sets (space M) {X -` B \<inter> space M |B. B \<in> sets N} \<subseteq> sets M" (is "?L \<subseteq> ?R")
  proof (rule sigma_algebra.sigma_sets_subset)
    show "{X -` B \<inter> space M |B. B \<in> sets N} \<subseteq> sets M"
    proof
      fix a
      assume "a \<in> {X -` B \<inter> (space M) | B. B \<in> sets N}"
      then obtain B where "B \<in> sets N" and "a = X -` B \<inter> (space M)" by auto
      thus "a \<in> sets M" using measurable_sets assms by simp
    qed
    show "sigma_algebra (space M) (sets M)" using measure_space by (auto simp add: measure_space_def)
  qed
  show "sigma_algebra (space M) ?L"
  proof (rule sigma_algebra_sigma_sets)
    let ?preimages = "{X -` B \<inter> (space M) | B. B \<in> sets N}"
    show "?preimages \<le> Pow (space M)" using assms by auto
  qed
qed

lemma fct_gen_subalgebra_fct_measurable:
  assumes "X \<in> space M \<rightarrow> space N"
  shows "X\<in> measurable (fct_gen_subalgebra M N X) N"
unfolding measurable_def
proof ((intro CollectI), (intro conjI))
  have speq: "space M = space (fct_gen_subalgebra M N X)"
      by (simp add: fct_gen_subalgebra_space)
  show "X \<in> space (fct_gen_subalgebra M N X) \<rightarrow> space N"
  proof -
    have "X \<in> space M \<rightarrow> space N"  using assms by simp
    thus ?thesis using speq by simp
  qed
  show "\<forall>y\<in>sets N.
       X -` y \<inter> space (fct_gen_subalgebra M N X) \<in> sets (fct_gen_subalgebra M N X)"
  using  fct_gen_subalgebra_sets_mem speq by metis
qed




lemma fct_gen_subalgebra_min:
  assumes "subalgebra M P"
  and "f\<in> measurable P N"
  shows "subalgebra P (fct_gen_subalgebra M N f)"
unfolding subalgebra_def
proof (intro conjI)
  let ?Mf = "fct_gen_subalgebra M N f"
  show "space ?Mf = space P" using assms
    by (simp add: fct_gen_subalgebra_def gen_subalgebra_space subalgebra_def)
  show inc: "sets ?Mf \<subseteq> sets P"
  proof -
    have "space M = space P" using assms by (simp add:subalgebra_def)
    have "f\<in> measurable M N" using assms using measurable_from_subalg by blast
    have "sigma_algebra (space P) (sets P)" using assms measure_space measure_space_def by auto
    have "\<forall> A \<in> sets N. f-`A \<inter> space P \<in> sets P" using assms by simp
    hence "{f -` A \<inter> (space M) | A. A \<in> sets N} \<subseteq> sets P" using \<open>space M = space P\<close> by auto
    hence "sigma_sets (space M) {f -` A \<inter> (space M) | A. A \<in> sets N} \<subseteq> sets P"
      by (simp add: \<open>sigma_algebra (space P) (sets P)\<close> \<open>space M = space P\<close> sigma_algebra.sigma_sets_subset)
    thus ?thesis using fct_gen_subalgebra_sets \<open>f \<in> M \<rightarrow>\<^sub>M N\<close> \<open>space M = space P\<close> assms(2)
      measurable_sets mem_Collect_eq sets.sigma_sets_subset subsetI by blast
  qed
qed

lemma fct_preimage_sigma_sets:
  assumes "X\<in> space M \<rightarrow> space N"
  shows "sigma_sets (space M) {X -` B \<inter> space M |B. B \<in> sets N} = {X -` B \<inter> space M |B. B \<in> sets N}" (is "?L = ?R")
proof
  show "?R\<subseteq> ?L" by blast
  show "?L\<subseteq> ?R"
  proof
    fix A
    assume "A\<in> ?L"
    thus "A\<in> ?R"
    proof (induct rule:sigma_sets.induct, auto)
      {
        fix B
        assume "B\<in> sets N"
        let ?cB = "space N - B"
        have "?cB \<in> sets N" by (simp add: \<open>B \<in> sets N\<close> sets.compl_sets)
        have "space M - X -` B \<inter> space M = X -` ?cB \<inter> space M"
        proof
          show "space M - X -` B \<inter> space M \<subseteq> X -` (space N - B) \<inter> space M"
          proof
            fix w
            assume "w \<in> space M - X -` B \<inter> space M"
            hence "X w \<in> (space N - B)" using assms by blast
            thus "w\<in> X -` (space N - B) \<inter> space M" using \<open>w \<in> space M - X -` B \<inter> space M\<close> by blast
          qed
          show "X -` (space N - B) \<inter> space M \<subseteq> space M - X -` B \<inter> space M"
          proof
            fix w
            assume "w\<in> X -` (space N - B) \<inter> space M"
            thus "w \<in> space M - X -` B \<inter> space M" by blast
          qed
        qed
        thus "\<exists>Ba. space M - X -` B \<inter> space M = X -` Ba \<inter> space M \<and> Ba \<in> sets N" using \<open>?cB \<in> sets N\<close> by auto
      }
      {
        fix S::"nat \<Rightarrow> 'a set"
        assume "(\<And>i. \<exists>B. S i = X -` B \<inter> space M \<and> B \<in> sets N)"
        hence "(\<forall>i. \<exists>B. S i = X -` B \<inter> space M \<and> B \<in> sets N)" by auto
        hence "\<exists> f. \<forall> x. S x = X -`(f x) \<inter> space M \<and> (f x) \<in> sets N"
          using choice[of "\<lambda>i B . S i = X -` B \<inter> space M \<and> B \<in> sets N"] by simp
        from this obtain rep where "\<forall>i. S i = X -` (rep i) \<inter> space M \<and> (rep i) \<in> sets N" by auto note rProp = this
        let ?uB = "\<Union>i\<in> UNIV. rep i"
        have "?uB \<in> sets N"
          by (simp add: \<open>\<forall>i. S i = X -` rep i \<inter> space M \<and> rep i \<in> sets N\<close> countable_Un_Int(1))
        have "(\<Union>x. S x) = X -` ?uB \<inter> space M"
        proof
          show "(\<Union>x. S x) \<subseteq> X -` (\<Union>i. rep i) \<inter> space M"
          proof
            fix w
            assume "w\<in> (\<Union>x. S x)"
            hence "\<exists>x. w \<in> S x" by auto
            from this obtain x where "w \<in> S x" by auto
            hence "w\<in>  X -` rep x \<inter> space M" using rProp by simp
            hence "w\<in> (\<Union>i. (X -`(rep i)\<inter> space M))" by blast
            also have "... = X -` (\<Union>i. rep i) \<inter> space M" by auto
            finally show "w \<in> X -` (\<Union>i. rep i) \<inter> space M" .
          qed
          show "X -` (\<Union>i. rep i) \<inter> space M \<subseteq> (\<Union>x. S x)"
          proof
            fix w
            assume "w\<in> X -` (\<Union>i. rep i) \<inter> space M"
            hence "\<exists> x. w\<in> X -` (rep x) \<inter> space M" by auto
            from this obtain x where "w\<in> X -` (rep x) \<inter> space M" by auto
            hence "w\<in> S x" using rProp by simp
            thus "w\<in> (\<Union>x. S x)" by blast
          qed
        qed
        thus "\<exists>B. (\<Union>x. S x) = X -` B \<inter> space M \<and> B \<in> sets N" using \<open>?uB \<in> sets N\<close> by auto
      }
    qed
  qed
qed

lemma fct_gen_subalgebra_sigma_sets:
  assumes "X\<in> space M \<rightarrow> space N"
  shows "sets (fct_gen_subalgebra M N X) = {X -` B \<inter> space M |B. B \<in> sets N}"
  by (simp add: assms fct_gen_subalgebra_sets fct_preimage_sigma_sets)


lemma fct_gen_subalgebra_info:
  assumes "f\<in> space M \<rightarrow> space N"
  and "x\<in> space M"
  and "w\<in> space M"
  and "f x = f w"
  shows "\<And>A. A\<in> sets (fct_gen_subalgebra M N f) \<Longrightarrow> (x\<in> A) = (w\<in> A)"
proof -
  {fix A
  assume "A \<in> sigma_sets (space M)  {f -` B \<inter> (space M) | B. B \<in> sets N}"
  from this have  "(x\<in> A) = (w\<in> A)"
  proof (induct rule:sigma_sets.induct)
    {
      fix a
      assume "a \<in> {f -` B \<inter> space M |B. B \<in> sets N}"
      hence "\<exists> B\<in> sets N. a = f -` B \<inter> space M" by auto
      from this obtain B where "B\<in> sets N" and "a = f -` B \<inter> space M" by blast note bhyps = this
      show "(x\<in> a) = (w\<in> a)" by (simp add: assms(2) assms(3) assms(4) bhyps(2))
    }
    {
      fix a
      assume "a \<in> sigma_sets (space M) {f -` B \<inter> space M |B. B \<in> sets N}"
      and "(x \<in> a) = (w \<in> a)" note xh = this
      show "(x \<in> space M - a) = (w \<in> space M - a)" by (simp add: assms(2) assms(3) xh(2))
    }
    {
      fix a::"nat \<Rightarrow> 'a set"
      assume "(\<And>i. a i \<in> sigma_sets (space M) {f -` B \<inter> space M |B. B \<in> sets N})"
      and "(\<And>i. (x \<in> a i) = (w \<in> a i))"
      show "(x \<in> \<Union>(a ` UNIV)) = (w \<in> \<Union>(a ` UNIV))" by (simp add: \<open>\<And>i. (x \<in> a i) = (w \<in> a i)\<close>)
    }
    {show "(x\<in> {}) = (w\<in> {})" by simp}
  qed} note eqsig = this
  fix A
  assume "A\<in> sets (fct_gen_subalgebra M N f)"
  hence "A \<in> sigma_sets (space M)  {f -` B \<inter> (space M) | B. B \<in> sets N}"
    using assms(1) fct_gen_subalgebra_sets by blast
  thus "(x\<in> A) = (w\<in> A)" using eqsig by simp
qed

subsection \<open>Independence between a random variable and a subalgebra.\<close>

definition (in prob_space) subalgebra_indep_var :: "('a \<Rightarrow> real) \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "subalgebra_indep_var X N \<longleftrightarrow>
    X\<in> borel_measurable M &
    (subalgebra M N) &
    (indep_set (sigma_sets (space M) { X -` A \<inter> space M | A. A \<in> sets borel}) (sets N))"


lemma (in prob_space) indep_set_mono:
  assumes "indep_set A B"
  assumes "A' \<subseteq> A"
  assumes "B' \<subseteq> B"
  shows "indep_set A' B'"
by (meson indep_sets2_eq assms subsetCE subset_trans)


lemma (in prob_space) subalgebra_indep_var_indicator:
  fixes X::"'a\<Rightarrow>real"
  assumes "subalgebra_indep_var X N"
  and "X \<in> borel_measurable M"
  and "A \<in> sets N"
  shows "indep_var borel X borel (indicator A)"
proof ((rule indep_var_eq[THEN iffD2]), (intro conjI))
  let ?IA = "(indicator A)::'a\<Rightarrow> real"
  show bm:"random_variable borel X" by (simp add: assms(2))
  show "random_variable borel ?IA" using assms indep_setD_ev2 unfolding subalgebra_indep_var_def by auto
  show "indep_set (sigma_sets (space M) {X -` A \<inter> space M |A. A \<in> sets borel})
   (sigma_sets (space M) {?IA -` Aa \<inter> space M |Aa. Aa \<in> sets borel})"
  proof (rule indep_set_mono)
    show "sigma_sets (space M) {X -` A \<inter> space M |A. A \<in> sets borel} \<subseteq> sigma_sets (space M) {X -` A \<inter> space M |A. A \<in> sets borel}" by simp
    show "sigma_sets (space M) {?IA -` B \<inter> space M |B. B \<in> sets borel} \<subseteq> sets N"
    proof -
      have "sigma_algebra (space M) (sets N)" using assms
        by (metis subalgebra_indep_var_def sets.sigma_algebra_axioms subalgebra_def)
      have "sigma_sets (space M) {?IA -` B \<inter> space M |B. B \<in> sets borel} \<subseteq> sigma_sets (space M) (sets N)"
      proof (rule sigma_sets_subseteq)
        show "{?IA -` B \<inter> space M |B. B \<in> sets borel} \<subseteq> sets N"
        proof
          fix x
          assume "x \<in> {?IA -` B \<inter> space M |B. B \<in> sets borel}"
          then obtain B where "B \<in> sets borel" and "x = ?IA -` B \<inter> space M" by auto
          thus "x \<in> sets N"
            by (metis (no_types, lifting) assms(1) assms(3) borel_measurable_indicator measurable_sets subalgebra_indep_var_def subalgebra_def)
        qed
      qed
      also have "... = sets N"
        by (simp add: \<open>sigma_algebra (space M) (sets N)\<close> sigma_algebra.sigma_sets_eq)
      finally show "sigma_sets (space M) {?IA -` B \<inter> space M |B. B \<in> sets borel} \<subseteq> sets N" .
    qed
    show "indep_set (sigma_sets (space M) {X -` A \<inter> space M |A. A \<in> sets borel}) (sets N) "
      using assms unfolding subalgebra_indep_var_def by simp
  qed
qed

lemma fct_gen_subalgebra_cong:
  assumes "space M = space P"
  and "sets N = sets Q"
  shows "fct_gen_subalgebra M N X = fct_gen_subalgebra P Q X"
proof -
  have "space M = space P" using assms by simp
  thus ?thesis using assms unfolding fct_gen_subalgebra_def gen_subalgebra_def by simp
qed



end