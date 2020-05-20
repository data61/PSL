(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Lebesgue Measure of Polynomial Zero Sets\<close>

theory Lebesgue_Zero_Set
  imports
    Polynomials.More_MPoly_Type
    Lebesgue_Functional
    Polynomials.MPoly_Type_Univariate
begin

lemma measurable_insertion [measurable]:
assumes "vars p \<subseteq> {..<n}"
shows "(\<lambda>f. insertion f p) \<in> borel_measurable (lborel_f n)"
using assms proof (induction p rule:mpoly_induct)
  case (monom m a)
  then show ?case
  proof (cases "a = 0")
    case True
    show ?thesis unfolding insertion_single \<open>a = 0\<close> MPoly_Type.monom.abs_eq single_zero
      zero_mpoly.abs_eq[symmetric] insertion_zero by measurable
  next
    case False
    have "Poly_Mapping.keys m \<subseteq> {..<n}" using monom by (simp add: False vars_monom_keys)
    then show ?thesis using \<open>a\<noteq>0\<close>
    proof (induction m arbitrary:a rule:poly_mapping_induct)
      case (single x i a)
      then show ?case
      proof (cases "i = 0")
        case True
        show ?thesis unfolding insertion_single \<open>i = 0\<close> by simp
      next
        case False
        then show ?thesis unfolding insertion_single apply measurable
          using vars_monom_single_cases single False insert_subset lessThan_iff \<open>a\<noteq>0\<close> by fastforce
      qed
    next
      case (sum m1 m2 x i)
      then have "Poly_Mapping.keys m1 \<inter> Poly_Mapping.keys m2 = {}" by simp
      then have "Poly_Mapping.keys m1 \<union> Poly_Mapping.keys m2 = Poly_Mapping.keys (m1 + m2)" using keys_add by metis
      then have 1:"Poly_Mapping.keys m1 \<subseteq> {..<n}" and 2:"Poly_Mapping.keys m2 \<subseteq> {..<n}" using sum.prems by auto
      show ?case unfolding MPoly_Type.mult_monom[of m1 a m2 1,simplified,symmetric]
        insertion_mult using sum.IH(1)[OF 1 \<open>a\<noteq>0\<close>] sum.IH(2)[OF 2, of 1, simplified] by measurable
    qed
  qed
next
  case (sum p1 p2 m a)
  then have "(\<lambda>f. insertion f p1) \<in> borel_measurable (lborel_f n)"
            "(\<lambda>f. insertion f p2) \<in> borel_measurable (lborel_f n)"
    using vars_add_monom[OF sum.hyps]  le_sup_iff by blast+
  then show ?case unfolding insertion_add by measurable
qed

text \<open>This proof follows Richard Caron and Tim Traynor, "The zero set of a polynomial"
http://www1.uwindsor.ca/math/sites/uwindsor.ca.math/files/05-03.pdf\<close>

lemma lebesgue_mpoly_zero_set:
fixes p::"real mpoly"
assumes "p \<noteq> 0" "vars p \<subseteq> {..<n}"
shows "{f\<in>space (lborel_f n). insertion f p = 0} \<in> null_sets (lborel_f n)"
using assms proof (induction n arbitrary:p)
  case 0
  then have "vars p = {}" by simp then have "\<And>f. insertion f p = MPoly_Type.coeff p 0"
      unfolding insertion_trivial[symmetric] using insertion_irrelevant_vars by blast
  have "\<And>m. m\<noteq>0 \<Longrightarrow> MPoly_Type.coeff p m = 0"
  proof (rule ccontr)
    fix m::"nat \<Rightarrow>\<^sub>0 nat" assume "m\<noteq>0" "MPoly_Type.coeff p m \<noteq> 0"
    then obtain v where "Poly_Mapping.lookup m v \<noteq> 0" using aux by auto
    then have "v\<in>vars p" unfolding More_MPoly_Type.vars_def using \<open>MPoly_Type.coeff p m \<noteq> 0\<close>
      by (meson UN_I coeff_keys lookup_not_eq_zero_eq_in_keys)
    then show False using \<open>vars p = {}\<close> by auto
  qed
  then have "MPoly_Type.coeff p 0 \<noteq> 0" using \<open>p \<noteq> 0\<close>
    by (metis coeff_all_0)
  then have "{f. insertion f p = 0} = {}" using \<open>\<And>f. insertion f p = MPoly_Type.coeff p 0\<close> by auto
  then show ?case by auto
next
  case (Suc n p)

text \<open>Show that N is finite:\<close>
  then have "extract_var p n \<noteq> 0" using reduce_nested_mpoly_0
    by (metis reduce_nested_mpoly_extract_var)
  let ?q = "\<lambda>j. MPoly_Type.coeff (extract_var p n) j"
  obtain j where "?q j \<noteq> 0" using \<open>extract_var p n \<noteq> 0\<close>
    by (metis coeff_all_0)
  then have "finite {x. insertion (\<lambda>_. x) (?q j) = 0}"
    using univariate_mpoly_roots_finite[OF vars_coeff_extract_var] by metis
  then have "finite (\<Inter>j. {x. insertion (\<lambda>_. x) (?q j) = 0})" by auto
  moreover have "{x. \<forall>j. insertion (\<lambda>_. x) (?q j) = 0} = (\<Inter>j. {x. insertion (\<lambda>v. x) (?q j) = 0})" by blast
  ultimately have "finite {x. \<forall>j. insertion (\<lambda>_. x) (?q j) = 0}" by metis

  define p_fix1 where "p_fix1 x1 = replace_coeff (insertion (\<lambda>_. x1)) (extract_var p n)" for x1
  define N where "N = {x1. p_fix1 x1 = 0}"
  have "N \<subseteq> {x. \<forall>j. insertion (\<lambda>_. x) (?q j) = 0}"
  proof
    fix x assume "x\<in>N"
    then have "p_fix1 x = 0" using N_def by auto
    then have "\<And>m. MPoly_Type.coeff (p_fix1 x) m = 0" by (metis More_MPoly_Type.coeff_monom monom_zero when_def)
    have "\<And>j. insertion (\<lambda>_. x) (?q j) = 0"
      using \<open>\<And>m. MPoly_Type.coeff (p_fix1 x) m = 0\<close>[unfolded p_fix1_def coeff_replace_coeff[of "insertion (\<lambda>_. x)", OF insertion_zero]]
      by metis
    then show "x \<in> {x. \<forall>j. insertion (\<lambda>_. x) (MPoly_Type.coeff (extract_var p n) j) = 0}" by blast
  qed
  then have "finite N" by (simp add: \<open>finite {x. \<forall>j. insertion (\<lambda>_. x) (MPoly_Type.coeff (extract_var p n) j) = 0}\<close> finite_subset)


text \<open>Use the IH:\<close>

  define A where "A = {f\<in>space (lborel_f (Suc n)). insertion f p = 0}"

  have "\<And>x1. vars (p_fix1 x1) \<subseteq> {..<n}"
  proof -
    fix x1
    have "vars (extract_var p n) \<subseteq> {..<n}"
      using \<open>vars p \<subseteq> {..<Suc n}\<close> lessThan_Suc v_not_in_vars_extract_var vars_extract_var_subset by fastforce
    then show "vars (p_fix1 x1) \<subseteq> {..<n}" unfolding p_fix1_def
      using vars_replace_coeff[of "insertion (\<lambda>_. x1)", OF insertion_zero] by blast
  qed
  have set_eq:"\<And>x1. {x \<in> space (lborel_f n). x(n := x1) \<in> A} = {f \<in> space (lborel_f n). insertion f (p_fix1 x1) = 0}"
  proof -
    fix x1
    show "{x\<in>space (lborel_f n). x(n := x1) \<in> A} = {f\<in>space (lborel_f n). insertion f (p_fix1 x1) = 0}"
    proof (rule subset_antisym;rule subsetI)
      fix x assume "x \<in> {x\<in>space (lborel_f n). x(n := x1) \<in> A}"
      then have "insertion (x(n := x1)) p = 0" "x \<in> space (lborel_f n)"
        using A_def by auto
      then have "insertion x (p_fix1 x1) = 0" unfolding p_fix1_def
        unfolding replace_coeff_extract_var_cong[of "\<lambda>_. x1" n "x(n := x1)" p, OF fun_upd_same[symmetric]]
        using insertion_replace_coeff[of "x(n := x1)"]
        using  insertion_irrelevant_vars[of "replace_coeff (insertion (x(n := x1))) (extract_var p n)" x "x(n := x1)"]
         vars_replace_coeff fun_upd_other insertion_zero reduce_nested_mpoly_extract_var subset_eq
         v_not_in_vars_extract_var by metis
      then show "x \<in> {f\<in>space (lborel_f n). insertion f (p_fix1 x1) = 0}" using \<open>x \<in> space (lborel_f n)\<close> by blast
    next
      fix f assume "f \<in> {f\<in>space (lborel_f n). insertion f (p_fix1 x1) = 0}"
      then have "f\<in>space (lborel_f n)" "insertion f (p_fix1 x1) = 0" by auto
      have "insertion (f(n := x1)) p = 0" using \<open>insertion f (p_fix1 x1) = 0\<close>[unfolded p_fix1_def]
        insertion_replace_coeff insertion_irrelevant_vars replace_coeff_extract_var_cong
        by (metis (no_types, lifting) \<open>insertion f (p_fix1 x1) = 0\<close> \<open>vars (p_fix1 x1) \<subseteq> {..<n}\<close>
        fun_upd_other fun_upd_same lessThan_iff order_less_irrefl p_fix1_def reduce_nested_mpoly_extract_var subsetCE)
      then have "f(n := x1) \<in> A" unfolding A_def using space_lborel_add_dim
        using \<open>f \<in> space (lborel_f n)\<close> lborel_f_def mem_Collect_eq by blast
      then show "f \<in> {f\<in>space (lborel_f n). f(n := x1) \<in> A}" using \<open>f \<in> space (lborel_f n)\<close> by auto
    qed
  qed

  have "\<And>x1. x1\<in>N \<Longrightarrow> {x\<in>space (lborel_f n). x(n := x1) \<in> A} \<in> sets (lborel_f n)"
       and emeasure_in_N: "\<And>x1. x1\<in>N \<Longrightarrow> emeasure (lborel_f n) {x\<in>space (lborel_f n). x(n := x1) \<in> A} = emeasure (lborel_f n) (space (lborel_f n))"
  proof -
    fix x1 assume "x1\<in>N"
    then have "p_fix1 x1 = 0" using N_def by auto
    then have "\<And>f. insertion f (p_fix1 x1) = 0" using insertion_zero by auto
    then have "{f \<in> space (lborel_f n). insertion f (p_fix1 x1) = 0} = space (lborel_f n)" by simp
    show "{x\<in>space (lborel_f n). x(n := x1) \<in> A} \<in> sets (lborel_f n)" unfolding set_eq
      by (simp add: \<open>{f \<in> space (lborel_f n). insertion f (p_fix1 x1) = 0} = space (lborel_f n)\<close>)
    show "emeasure (lborel_f n) {x\<in>space (lborel_f n). x(n := x1) \<in> A} = emeasure (lborel_f n) (space (lborel_f n))"
      unfolding set_eq
      by (simp add: \<open>{f \<in> space (lborel_f n). insertion f (p_fix1 x1) = 0} = space (lborel_f n)\<close>)
  qed

  have emeasure_not_in_N: "\<And>x1. x1\<notin>N \<Longrightarrow> emeasure (lborel_f n) {x\<in>space (lborel_f n). x(n := x1) \<in> A} = 0"
       and "\<And>x1. x1\<notin>N \<Longrightarrow> {x\<in>space (lborel_f n). x(n := x1) \<in> A} \<in> sets (lborel_f n)"
  proof -
    fix x1 assume "x1\<notin>N"
    then have "p_fix1 x1 \<noteq> 0" using p_fix1_def N_def by auto
    then have "emeasure (lborel_f n) {f\<in>space (lborel_f n). insertion f (p_fix1 x1) = 0} = 0"
              "{f\<in>space (lborel_f n). insertion f (p_fix1 x1) = 0} \<in> sets (lborel_f n)"
      using Suc.IH[OF \<open>p_fix1 x1 \<noteq> 0\<close>] \<open>\<And>x1. vars (p_fix1 x1) \<subseteq> {..<n}\<close> by auto
    then show "emeasure (lborel_f n) {x\<in>space (lborel_f n). x(n := x1) \<in> A} = 0"
      "{x\<in>space (lborel_f n). x(n := x1) \<in> A} \<in> sets (lborel_f n)"
      using \<open>{f\<in>space (lborel_f n). insertion f (p_fix1 x1) = 0} \<in> sets (lborel_f n)\<close>
        \<open>emeasure (lborel_f n) {f\<in>space (lborel_f n). insertion f (p_fix1 x1) = 0} = 0\<close>
      using set_eq
      by auto
  qed

  have "N \<in> null_sets lborel" using \<open>finite N\<close> finite_imp_null_set_lborel by blast
  have ae_zero: "AE x1 in lborel. emeasure (lborel_f n) {x \<in> space (lborel_f n). x(n := x1) \<in> A} = 0"
    apply (rule AE_I'[OF \<open>N \<in> null_sets lborel\<close>])
    using \<open>\<And>x1. x1\<notin>N \<Longrightarrow> emeasure (lborel_f n) {x\<in>space (lborel_f n). x(n := x1) \<in> A} = 0\<close>
    by force

  have measurable: "(\<lambda>x1. emeasure (lborel_f n) {x \<in> space (lborel_f n). x(n := x1) \<in> A}) \<in> borel_measurable lborel"
  proof (rule borel_measurableI)
    let ?f = "(\<lambda>x1. emeasure (lborel_f n) {x \<in> space (lborel_f n). x(n := x1) \<in> A})"
    fix S::"ennreal set" assume "open S"
    have 0:"0\<in>S \<Longrightarrow> - N \<subseteq> ?f -` S"
      using emeasure_not_in_N by auto
    have 1:"emeasure (lborel_f n) (space (lborel_f n)) \<in> S \<Longrightarrow> N \<subseteq> ?f -` S"
      using emeasure_in_N by auto
    have 2:"0\<notin>S \<Longrightarrow> ?f -` S \<subseteq> N" using emeasure_not_in_N by fastforce
    have 3:"emeasure (lborel_f n) (space (lborel_f n)) \<notin> S \<Longrightarrow> ?f -` S \<subseteq> -N" using emeasure_in_N by auto
    have "?f -` S = {} \<or> ?f -` S = N \<or> ?f -` S = UNIV \<or> ?f -` S = - N"
      apply (cases "0\<in>S"; cases "emeasure (lborel_f n) (space (lborel_f n)) \<notin> S")
      using 0 1 2 3 by auto
    then show "?f -` S  \<inter> space lborel \<in> sets lborel"
      using \<open>finite N\<close> finite_imp_null_set_lborel borel_comp null_setsD2 sets_lborel by fastforce
  qed

  have "A \<in> sets (lborel_f (Suc n))" unfolding A_def
    using pred_eq_const1[OF measurable_insertion[OF \<open>vars p \<subseteq> {..<Suc n}\<close>]] pred_def by force
  then have in_sets: "{f \<in> space (lborel_f (Suc n)). insertion f p = 0} \<in> sets (lborel_f (Suc n))" using A_def by metis
  have "\<And>x1. {x\<in>space (lborel_f n). x(n := x1) \<in> A} \<in> sets (lborel_f n)"
    using \<open>\<And>x1. x1\<in>N \<Longrightarrow> {x\<in>space (lborel_f n). x(n := x1) \<in> A} \<in> sets (lborel_f n)\<close>
    \<open>\<And>x1. x1\<notin>N \<Longrightarrow> {x\<in>space (lborel_f n). x(n := x1) \<in> A} \<in> sets (lborel_f n)\<close> by auto
  have "emeasure (lborel_f (Suc n)) A = \<integral>\<^sup>+ y. emeasure (lborel_f n) {x \<in> space (lborel_f n). x(n := y) \<in> A} \<partial>lborel"
    using emeasure_lborel_f_Suc[OF \<open>A \<in> sets (lborel_f (Suc n))\<close>]
     \<open>\<And>x1. {x\<in>space (lborel_f n). x(n := x1) \<in> A} \<in> sets (lborel_f n)\<close> by blast
  also have "... = 0"
    using nn_integral_0_iff_AE[OF measurable] ae_zero by blast
  finally have "emeasure (lborel_f (Suc n)) A = 0" by auto
  then show ?case unfolding null_sets_def using in_sets A_def by blast
qed

end
