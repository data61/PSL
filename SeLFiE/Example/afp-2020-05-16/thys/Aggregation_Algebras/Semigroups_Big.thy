(* Title:      Big Sum over Finite Sets in Abelian Semigroups
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

(*  Title:      HOL/Groups_Big.thy
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Markus Wenzel
    Author:     Jeremy Avigad
*)

section \<open>Big Sum over Finite Sets in Abelian Semigroups\<close>

theory Semigroups_Big
  imports Main
begin

text \<open>
This theory is based on Isabelle/HOL's \<open>Groups_Big.thy\<close> written by T. Nipkow, L. C. Paulson, M. Wenzel and J. Avigad.
We have generalised a selection of its results from Abelian monoids to Abelian semigroups with an element that is a unit on the image of the semigroup operation.
\<close>

subsection \<open>Generic Abelian semigroup operation over a set\<close>

locale abel_semigroup_set = abel_semigroup +
  fixes z :: 'a ("\<^bold>1")
  assumes z_neutral [simp]: "x \<^bold>* y \<^bold>* \<^bold>1 = x \<^bold>* y"
  assumes z_idem [simp]: "\<^bold>1 \<^bold>* \<^bold>1 = \<^bold>1"
begin

interpretation comp_fun_commute f
  by standard (simp add: fun_eq_iff left_commute)

interpretation comp?: comp_fun_commute "f \<circ> g"
  by (fact comp_comp_fun_commute)

definition F :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
  where eq_fold: "F g A = Finite_Set.fold (f \<circ> g) \<^bold>1 A"

lemma infinite [simp]: "\<not> finite A \<Longrightarrow> F g A = \<^bold>1"
  by (simp add: eq_fold)

lemma empty [simp]: "F g {} = \<^bold>1"
  by (simp add: eq_fold)

lemma insert [simp]: "finite A \<Longrightarrow> x \<notin> A \<Longrightarrow> F g (insert x A) = g x \<^bold>* F g A"
  by (simp add: eq_fold)

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F g A = g x \<^bold>* F g (A - {x})"
proof -
  from \<open>x \<in> A\<close> obtain B where B: "A = insert x B" and "x \<notin> B"
    by (auto dest: mk_disjoint_insert)
  moreover from \<open>finite A\<close> B have "finite B" by simp
  ultimately show ?thesis by simp
qed

lemma insert_remove: "finite A \<Longrightarrow> F g (insert x A) = g x \<^bold>* F g (A - {x})"
  by (cases "x \<in> A") (simp_all add: remove insert_absorb)

lemma insert_if: "finite A \<Longrightarrow> F g (insert x A) = (if x \<in> A then F g A else g x \<^bold>* F g A)"
  by (cases "x \<in> A") (simp_all add: insert_absorb)

lemma neutral: "\<forall>x\<in>A. g x = \<^bold>1 \<Longrightarrow> F g A = \<^bold>1"
  by (induct A rule: infinite_finite_induct) simp_all

lemma neutral_const [simp]: "F (\<lambda>_. \<^bold>1) A = \<^bold>1"
  by (simp add: neutral)

lemma F_one [simp]: "F g A \<^bold>* \<^bold>1 = F g A"
proof -
  have "\<And>f b B. F f (insert (b::'b) B) \<^bold>* \<^bold>1 = F f (insert b B) \<or> infinite B"
    using insert_remove by fastforce
  then show ?thesis
    by (metis (no_types) all_not_in_conv empty z_idem infinite insert_if)
qed

lemma one_F [simp]: "\<^bold>1 \<^bold>* F g A = F g A"
  using F_one commute by auto

lemma F_g_one [simp]: "F (\<lambda>x . g x \<^bold>* \<^bold>1) A = F g A"
  apply (induct A rule: infinite_finite_induct)
  apply simp
  apply simp
  by (metis one_F assoc insert)

lemma union_inter:
  assumes "finite A" and "finite B"
  shows "F g (A \<union> B) \<^bold>* F g (A \<inter> B) = F g A \<^bold>* F g B"
  \<comment> \<open>The reversed orientation looks more natural, but LOOPS as a simprule!\<close>
  using assms
proof (induct A)
  case empty
  then show ?case by simp
next
  case (insert x A)
  then show ?case
    by (auto simp: insert_absorb Int_insert_left commute [of _ "g x"] assoc left_commute)
qed

corollary union_inter_neutral:
  assumes "finite A" and "finite B"
    and "\<forall>x \<in> A \<inter> B. g x = \<^bold>1"
  shows "F g (A \<union> B) = F g A \<^bold>* F g B"
  using assms by (simp add: union_inter [symmetric] neutral)

corollary union_disjoint:
  assumes "finite A" and "finite B"
  assumes "A \<inter> B = {}"
  shows "F g (A \<union> B) = F g A \<^bold>* F g B"
  using assms by (simp add: union_inter_neutral)

lemma union_diff2:
  assumes "finite A" and "finite B"
  shows "F g (A \<union> B) = F g (A - B) \<^bold>* F g (B - A) \<^bold>* F g (A \<inter> B)"
proof -
  have "A \<union> B = A - B \<union> (B - A) \<union> A \<inter> B"
    by auto
  with assms show ?thesis
    by simp (subst union_disjoint, auto)+
qed

lemma subset_diff:
  assumes "B \<subseteq> A" and "finite A"
  shows "F g A = F g (A - B) \<^bold>* F g B"
proof -
  from assms have "finite (A - B)" by auto
  moreover from assms have "finite B" by (rule finite_subset)
  moreover from assms have "(A - B) \<inter> B = {}" by auto
  ultimately have "F g (A - B \<union> B) = F g (A - B) \<^bold>* F g B" by (rule union_disjoint)
  moreover from assms have "A \<union> B = A" by auto
  ultimately show ?thesis by simp
qed

lemma setdiff_irrelevant:
  assumes "finite A"
  shows "F g (A - {x. g x = z}) = F g A"
  using assms by (induct A) (simp_all add: insert_Diff_if)

lemma not_neutral_contains_not_neutral:
  assumes "F g A \<noteq> \<^bold>1"
  obtains a where "a \<in> A" and "g a \<noteq> \<^bold>1"
proof -
  from assms have "\<exists>a\<in>A. g a \<noteq> \<^bold>1"
  proof (induct A rule: infinite_finite_induct)
    case infinite
    then show ?case by simp
  next
    case empty
    then show ?case by simp
  next
    case (insert a A)
    then show ?case by fastforce
  qed
  with that show thesis by blast
qed

lemma reindex:
  assumes "inj_on h A"
  shows "F g (h ` A) = F (g \<circ> h) A"
proof (cases "finite A")
  case True
  with assms show ?thesis
    by (simp add: eq_fold fold_image comp_assoc)
next
  case False
  with assms have "\<not> finite (h ` A)" by (blast dest: finite_imageD)
  with False show ?thesis by simp
qed

lemma cong [fundef_cong]:
  assumes "A = B"
  assumes g_h: "\<And>x. x \<in> B \<Longrightarrow> g x = h x"
  shows "F g A = F h B"
  using g_h unfolding \<open>A = B\<close>
  by (induct B rule: infinite_finite_induct) auto

lemma strong_cong [cong]:
  assumes "A = B" "\<And>x. x \<in> B =simp=> g x = h x"
  shows "F (\<lambda>x. g x) A = F (\<lambda>x. h x) B"
  by (rule cong) (use assms in \<open>simp_all add: simp_implies_def\<close>)

lemma reindex_cong:
  assumes "inj_on l B"
  assumes "A = l ` B"
  assumes "\<And>x. x \<in> B \<Longrightarrow> g (l x) = h x"
  shows "F g A = F h B"
  using assms by (simp add: reindex)

lemma UNION_disjoint:
  assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
    and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
  shows "F g (\<Union>(A ` I)) = F (\<lambda>x. F g (A x)) I"
  apply (insert assms)
  apply (induct rule: finite_induct)
   apply simp
  apply atomize
  apply (subgoal_tac "\<forall>i\<in>Fa. x \<noteq> i")
   prefer 2 apply blast
  apply (subgoal_tac "A x \<inter> \<Union>(A ` Fa) = {}")
   prefer 2 apply blast
  apply (simp add: union_disjoint)
  done

lemma Union_disjoint:
  assumes "\<forall>A\<in>C. finite A" "\<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
  shows "F g (\<Union>C) = (F \<circ> F) g C"
proof (cases "finite C")
  case True
  from UNION_disjoint [OF this assms] show ?thesis by simp
next
  case False
  then show ?thesis by (auto dest: finite_UnionD intro: infinite)
qed

lemma distrib: "F (\<lambda>x. g x \<^bold>* h x) A = F g A \<^bold>* F h A"
  by (induct A rule: infinite_finite_induct) (simp_all add: assoc commute left_commute)

lemma Sigma:
  "finite A \<Longrightarrow> \<forall>x\<in>A. finite (B x) \<Longrightarrow> F (\<lambda>x. F (g x) (B x)) A = F (case_prod g) (SIGMA x:A. B x)"
  apply (subst Sigma_def)
  apply (subst UNION_disjoint)
     apply assumption
    apply simp
   apply blast
  apply (rule cong)
   apply rule
  apply (simp add: fun_eq_iff)
  apply (subst UNION_disjoint)
     apply simp
    apply simp
   apply blast
  apply (simp add: comp_def)
  done

lemma related:
  assumes Re: "R \<^bold>1 \<^bold>1"
    and Rop: "\<forall>x1 y1 x2 y2. R x1 x2 \<and> R y1 y2 \<longrightarrow> R (x1 \<^bold>* y1) (x2 \<^bold>* y2)"
    and fin: "finite S"
    and R_h_g: "\<forall>x\<in>S. R (h x) (g x)"
  shows "R (F h S) (F g S)"
  using fin by (rule finite_subset_induct) (use assms in auto)

lemma mono_neutral_cong_left:
  assumes "finite T"
    and "S \<subseteq> T"
    and "\<forall>i \<in> T - S. h i = \<^bold>1"
    and "\<And>x. x \<in> S \<Longrightarrow> g x = h x"
  shows "F g S = F h T"
proof-
  have eq: "T = S \<union> (T - S)" using \<open>S \<subseteq> T\<close> by blast
  have d: "S \<inter> (T - S) = {}" using \<open>S \<subseteq> T\<close> by blast
  from \<open>finite T\<close> \<open>S \<subseteq> T\<close> have f: "finite S" "finite (T - S)"
    by (auto intro: finite_subset)
  show ?thesis using assms(4)
    by (simp add: union_disjoint [OF f d, unfolded eq [symmetric]] neutral [OF assms(3)])
qed

lemma mono_neutral_cong_right:
  "finite T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> \<forall>i \<in> T - S. g i = \<^bold>1 \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> g x = h x) \<Longrightarrow>
    F g T = F h S"
  by (auto intro!: mono_neutral_cong_left [symmetric])

lemma mono_neutral_left: "finite T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> \<forall>i \<in> T - S. g i = \<^bold>1 \<Longrightarrow> F g S = F g T"
  by (blast intro: mono_neutral_cong_left)

lemma mono_neutral_right: "finite T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> \<forall>i \<in> T - S. g i = \<^bold>1 \<Longrightarrow> F g T = F g S"
  by (blast intro!: mono_neutral_left [symmetric])

lemma mono_neutral_cong:
  assumes [simp]: "finite T" "finite S"
    and *: "\<And>i. i \<in> T - S \<Longrightarrow> h i = \<^bold>1" "\<And>i. i \<in> S - T \<Longrightarrow> g i = \<^bold>1"
    and gh: "\<And>x. x \<in> S \<inter> T \<Longrightarrow> g x = h x"
 shows "F g S = F h T"
proof-
  have "F g S = F g (S \<inter> T)"
    by(rule mono_neutral_right)(auto intro: *)
  also have "\<dots> = F h (S \<inter> T)" using refl gh by(rule cong)
  also have "\<dots> = F h T"
    by(rule mono_neutral_left)(auto intro: *)
  finally show ?thesis .
qed

lemma reindex_bij_betw: "bij_betw h S T \<Longrightarrow> F (\<lambda>x. g (h x)) S = F g T"
  by (auto simp: bij_betw_def reindex)

lemma reindex_bij_witness:
  assumes witness:
    "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
    "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
    "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
    "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
  assumes eq:
    "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  shows "F g S = F h T"
proof -
  have "bij_betw j S T"
    using bij_betw_byWitness[where A=S and f=j and f'=i and A'=T] witness by auto
  moreover have "F g S = F (\<lambda>x. h (j x)) S"
    by (intro cong) (auto simp: eq)
  ultimately show ?thesis
    by (simp add: reindex_bij_betw)
qed

lemma reindex_bij_betw_not_neutral:
  assumes fin: "finite S'" "finite T'"
  assumes bij: "bij_betw h (S - S') (T - T')"
  assumes nn:
    "\<And>a. a \<in> S' \<Longrightarrow> g (h a) = z"
    "\<And>b. b \<in> T' \<Longrightarrow> g b = z"
  shows "F (\<lambda>x. g (h x)) S = F g T"
proof -
  have [simp]: "finite S \<longleftrightarrow> finite T"
    using bij_betw_finite[OF bij] fin by auto
  show ?thesis
  proof (cases "finite S")
    case True
    with nn have "F (\<lambda>x. g (h x)) S = F (\<lambda>x. g (h x)) (S - S')"
      by (intro mono_neutral_cong_right) auto
    also have "\<dots> = F g (T - T')"
      using bij by (rule reindex_bij_betw)
    also have "\<dots> = F g T"
      using nn \<open>finite S\<close> by (intro mono_neutral_cong_left) auto
    finally show ?thesis .
  next
    case False
    then show ?thesis by simp
  qed
qed

lemma reindex_nontrivial:
  assumes "finite A"
    and nz: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> h x = h y \<Longrightarrow> g (h x) = \<^bold>1"
  shows "F g (h ` A) = F (g \<circ> h) A"
proof (subst reindex_bij_betw_not_neutral [symmetric])
  show "bij_betw h (A - {x \<in> A. (g \<circ> h) x = \<^bold>1}) (h ` A - h ` {x \<in> A. (g \<circ> h) x = \<^bold>1})"
    using nz by (auto intro!: inj_onI simp: bij_betw_def)
qed (use \<open>finite A\<close> in auto)

lemma reindex_bij_witness_not_neutral:
  assumes fin: "finite S'" "finite T'"
  assumes witness:
    "\<And>a. a \<in> S - S' \<Longrightarrow> i (j a) = a"
    "\<And>a. a \<in> S - S' \<Longrightarrow> j a \<in> T - T'"
    "\<And>b. b \<in> T - T' \<Longrightarrow> j (i b) = b"
    "\<And>b. b \<in> T - T' \<Longrightarrow> i b \<in> S - S'"
  assumes nn:
    "\<And>a. a \<in> S' \<Longrightarrow> g a = z"
    "\<And>b. b \<in> T' \<Longrightarrow> h b = z"
  assumes eq:
    "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  shows "F g S = F h T"
proof -
  have bij: "bij_betw j (S - (S' \<inter> S)) (T - (T' \<inter> T))"
    using witness by (intro bij_betw_byWitness[where f'=i]) auto
  have F_eq: "F g S = F (\<lambda>x. h (j x)) S"
    by (intro cong) (auto simp: eq)
  show ?thesis
    unfolding F_eq using fin nn eq
    by (intro reindex_bij_betw_not_neutral[OF _ _ bij]) auto
qed

lemma delta_remove:
  assumes fS: "finite S"
  shows "F (\<lambda>k. if k = a then b k else c k) S = (if a \<in> S then b a \<^bold>* F c (S-{a}) else F c (S-{a}))"
proof -
  let ?f = "(\<lambda>k. if k = a then b k else c k)"
  show ?thesis
  proof (cases "a \<in> S")
    case False
    then have "\<forall>k\<in>S. ?f k = c k" by simp
    with False show ?thesis by simp
  next
    case True
    let ?A = "S - {a}"
    let ?B = "{a}"
    from True have eq: "S = ?A \<union> ?B" by blast
    have dj: "?A \<inter> ?B = {}" by simp
    from fS have fAB: "finite ?A" "finite ?B" by auto
    have "F ?f S = F ?f ?A \<^bold>* F ?f ?B"
      using union_disjoint [OF fAB dj, of ?f, unfolded eq [symmetric]] by simp
    with True show ?thesis
      using abel_semigroup_set.remove abel_semigroup_set_axioms fS by fastforce
  qed
qed

lemma delta [simp]:
  assumes fS: "finite S"
  shows "F (\<lambda>k. if k = a then b k else \<^bold>1) S = (if a \<in> S then b a \<^bold>* \<^bold>1 else \<^bold>1)"
  by (simp add: delta_remove [OF assms])

lemma delta' [simp]:
  assumes fin: "finite S"
  shows "F (\<lambda>k. if a = k then b k else \<^bold>1) S = (if a \<in> S then b a \<^bold>* \<^bold>1 else \<^bold>1)"
  using delta [OF fin, of a b, symmetric] by (auto intro: cong)

lemma If_cases:
  fixes P :: "'b \<Rightarrow> bool" and g h :: "'b \<Rightarrow> 'a"
  assumes fin: "finite A"
  shows "F (\<lambda>x. if P x then h x else g x) A = F h (A \<inter> {x. P x}) \<^bold>* F g (A \<inter> - {x. P x})"
proof -
  have a: "A = A \<inter> {x. P x} \<union> A \<inter> -{x. P x}" "(A \<inter> {x. P x}) \<inter> (A \<inter> -{x. P x}) = {}"
    by blast+
  from fin have f: "finite (A \<inter> {x. P x})" "finite (A \<inter> -{x. P x})" by auto
  let ?g = "\<lambda>x. if P x then h x else g x"
  from union_disjoint [OF f a(2), of ?g] a(1) show ?thesis
    by (subst (1 2) cong) simp_all
qed

lemma cartesian_product: "F (\<lambda>x. F (g x) B) A = F (case_prod g) (A \<times> B)"
  apply (rule sym)
  apply (cases "finite A")
   apply (cases "finite B")
    apply (simp add: Sigma)
   apply (cases "A = {}")
    apply simp
   apply simp
   apply (auto intro: infinite dest: finite_cartesian_productD2)
  apply (cases "B = {}")
   apply (auto intro: infinite dest: finite_cartesian_productD1)
  done

lemma inter_restrict:
  assumes "finite A"
  shows "F g (A \<inter> B) = F (\<lambda>x. if x \<in> B then g x else \<^bold>1) A"
proof -
  let ?g = "\<lambda>x. if x \<in> A \<inter> B then g x else \<^bold>1"
  have "\<forall>i\<in>A - A \<inter> B. (if i \<in> A \<inter> B then g i else \<^bold>1) = \<^bold>1" by simp
  moreover have "A \<inter> B \<subseteq> A" by blast
  ultimately have "F ?g (A \<inter> B) = F ?g A"
    using \<open>finite A\<close> by (intro mono_neutral_left) auto
  then show ?thesis by simp
qed

lemma inter_filter:
  "finite A \<Longrightarrow> F g {x \<in> A. P x} = F (\<lambda>x. if P x then g x else \<^bold>1) A"
  by (simp add: inter_restrict [symmetric, of A "{x. P x}" g, simplified mem_Collect_eq] Int_def)

lemma Union_comp:
  assumes "\<forall>A \<in> B. finite A"
    and "\<And>A1 A2 x. A1 \<in> B \<Longrightarrow> A2 \<in> B \<Longrightarrow> A1 \<noteq> A2 \<Longrightarrow> x \<in> A1 \<Longrightarrow> x \<in> A2 \<Longrightarrow> g x = \<^bold>1"
  shows "F g (\<Union>B) = (F \<circ> F) g B"
  using assms
proof (induct B rule: infinite_finite_induct)
  case (infinite A)
  then have "\<not> finite (\<Union>A)" by (blast dest: finite_UnionD)
  with infinite show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert A B)
  then have "finite A" "finite B" "finite (\<Union>B)" "A \<notin> B"
    and "\<forall>x\<in>A \<inter> \<Union>B. g x = \<^bold>1"
    and H: "F g (\<Union>B) = (F \<circ> F) g B" by auto
  then have "F g (A \<union> \<Union>B) = F g A \<^bold>* F g (\<Union>B)"
    by (simp add: union_inter_neutral)
  with \<open>finite B\<close> \<open>A \<notin> B\<close> show ?case
    by (simp add: H)
qed

lemma swap: "F (\<lambda>i. F (g i) B) A = F (\<lambda>j. F (\<lambda>i. g i j) A) B"
  unfolding cartesian_product
  by (rule reindex_bij_witness [where i = "\<lambda>(i, j). (j, i)" and j = "\<lambda>(i, j). (j, i)"]) auto

lemma swap_restrict:
  "finite A \<Longrightarrow> finite B \<Longrightarrow>
    F (\<lambda>x. F (g x) {y. y \<in> B \<and> R x y}) A = F (\<lambda>y. F (\<lambda>x. g x y) {x. x \<in> A \<and> R x y}) B"
  by (simp add: inter_filter) (rule swap)

lemma Plus:
  fixes A :: "'b set" and B :: "'c set"
  assumes fin: "finite A" "finite B"
  shows "F g (A <+> B) = F (g \<circ> Inl) A \<^bold>* F (g \<circ> Inr) B"
proof -
  have "A <+> B = Inl ` A \<union> Inr ` B" by auto
  moreover from fin have "finite (Inl ` A)" "finite (Inr ` B)" by auto
  moreover have "Inl ` A \<inter> Inr ` B = {}" by auto
  moreover have "inj_on Inl A" "inj_on Inr B" by (auto intro: inj_onI)
  ultimately show ?thesis
    using fin by (simp add: union_disjoint reindex)
qed

lemma same_carrier:
  assumes "finite C"
  assumes subset: "A \<subseteq> C" "B \<subseteq> C"
  assumes trivial: "\<And>a. a \<in> C - A \<Longrightarrow> g a = \<^bold>1" "\<And>b. b \<in> C - B \<Longrightarrow> h b = \<^bold>1"
  shows "F g A = F h B \<longleftrightarrow> F g C = F h C"
proof -
  have "finite A" and "finite B" and "finite (C - A)" and "finite (C - B)"
    using \<open>finite C\<close> subset by (auto elim: finite_subset)
  from subset have [simp]: "A - (C - A) = A" by auto
  from subset have [simp]: "B - (C - B) = B" by auto
  from subset have "C = A \<union> (C - A)" by auto
  then have "F g C = F g (A \<union> (C - A))" by simp
  also have "\<dots> = F g (A - (C - A)) \<^bold>* F g (C - A - A) \<^bold>* F g (A \<inter> (C - A))"
    using \<open>finite A\<close> \<open>finite (C - A)\<close> by (simp only: union_diff2)
  finally have *: "F g C = F g A" using trivial by simp
  from subset have "C = B \<union> (C - B)" by auto
  then have "F h C = F h (B \<union> (C - B))" by simp
  also have "\<dots> = F h (B - (C - B)) \<^bold>* F h (C - B - B) \<^bold>* F h (B \<inter> (C - B))"
    using \<open>finite B\<close> \<open>finite (C - B)\<close> by (simp only: union_diff2)
  finally have "F h C = F h B"
    using trivial by simp
  with * show ?thesis by simp
qed

lemma same_carrierI:
  assumes "finite C"
  assumes subset: "A \<subseteq> C" "B \<subseteq> C"
  assumes trivial: "\<And>a. a \<in> C - A \<Longrightarrow> g a = \<^bold>1" "\<And>b. b \<in> C - B \<Longrightarrow> h b = \<^bold>1"
  assumes "F g C = F h C"
  shows "F g A = F h B"
  using assms same_carrier [of C A B] by simp

end


subsection \<open>Generalized summation over a set\<close>

no_notation Sum ("\<Sum>")

class ab_semigroup_add_0 = zero + ab_semigroup_add +
  assumes zero_neutral [simp]: "x + y + 0 = x + y"
  assumes zero_idem [simp]: "0 + 0 = 0"
begin

sublocale sum_0: abel_semigroup_set plus 0
  defines sum_0 = sum_0.F
  by unfold_locales simp_all

abbreviation Sum_0 ("\<Sum>")
  where "\<Sum> \<equiv> sum_0 (\<lambda>x. x)"

end

context comm_monoid_add
begin

subclass ab_semigroup_add_0
  by unfold_locales simp_all

end

text \<open>Now: lots of fancy syntax. First, @{term "sum_0 (\<lambda>x. e) A"} is written \<open>\<Sum>x\<in>A. e\<close>.\<close>

syntax (ASCII)
  "_sum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::comm_monoid_add"  ("(3SUM (_/:_)./ _)" [0, 51, 10] 10)
syntax
  "_sum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::comm_monoid_add"  ("(2\<Sum>(_/\<in>_)./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Sum>i\<in>A. b" \<rightleftharpoons> "CONST sum_0 (\<lambda>i. b) A"

text \<open>Instead of @{term"\<Sum>x\<in>{x. P}. e"} we introduce the shorter \<open>\<Sum>x|P. e\<close>.\<close>

syntax (ASCII)
  "_qsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(3SUM _ |/ _./ _)" [0, 0, 10] 10)
syntax
  "_qsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<Sum>_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Sum>x|P. t" => "CONST sum_0 (\<lambda>x. t) {x. P}"

print_translation \<open>
let
  fun sum_tr' [Abs (x, Tx, t), Const (@{const_syntax Collect}, _) $ Abs (y, Ty, P)] =
        if x <> y then raise Match
        else
          let
            val x' = Syntax_Trans.mark_bound_body (x, Tx);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in
            Syntax.const @{syntax_const "_qsum"} $ Syntax_Trans.mark_bound_abs (x, Tx) $ P' $ t'
          end
    | sum_tr' _ = raise Match;
in [(@{const_syntax sum_0}, K sum_tr')] end
\<close>

lemma (in ab_semigroup_add_0) sum_image_gen_0:
  assumes fin: "finite S"
  shows "sum_0 g S = sum_0 (\<lambda>y. sum_0 g {x. x \<in> S \<and> f x = y}) (f ` S)"
proof -
  have "{y. y\<in> f`S \<and> f x = y} = {f x}" if "x \<in> S" for x
    using that by auto
  then have "sum_0 g S = sum_0 (\<lambda>x. sum_0 (\<lambda>y. g x) {y. y\<in> f`S \<and> f x = y}) S"
    by simp
  also have "\<dots> = sum_0 (\<lambda>y. sum_0 g {x. x \<in> S \<and> f x = y}) (f ` S)"
    by (rule sum_0.swap_restrict [OF fin finite_imageI [OF fin]])
  finally show ?thesis .
qed


subsubsection \<open>Properties in more restricted classes of structures\<close>

lemma sum_Un2:
  assumes "finite (A \<union> B)"
  shows "sum_0 f (A \<union> B) = sum_0 f (A - B) + sum_0 f (B - A) + sum_0 f (A \<inter> B)"
proof -
  have "A \<union> B = A - B \<union> (B - A) \<union> A \<inter> B"
    by auto
  with assms show ?thesis
    by simp (subst sum_0.union_disjoint, auto)+
qed

class ordered_ab_semigroup_add_0 = ab_semigroup_add_0 + ordered_ab_semigroup_add
begin

lemma add_nonneg_nonneg [simp]: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a + b"
  using add_mono[of 0 a 0 b] by simp

lemma add_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> a + b \<le> 0"
  using add_mono[of a 0 b 0] by simp

end

lemma (in ordered_ab_semigroup_add_0) sum_mono:
  "(\<And>i. i\<in>K \<Longrightarrow> f i \<le> g i) \<Longrightarrow> (\<Sum>i\<in>K. f i) \<le> (\<Sum>i\<in>K. g i)"
  by (induct K rule: infinite_finite_induct) (use add_mono in auto)

lemma (in ordered_ab_semigroup_add_0) sum_mono_00:
  "(\<And>i. i\<in>K \<Longrightarrow> f i + 0 \<le> g i + 0) \<Longrightarrow> (\<Sum>i\<in>K. f i) \<le> (\<Sum>i\<in>K. g i)"
proof (induct K rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case
  proof -
    fix x :: 'b and F :: "'b set"
    assume a1: "finite F"
    assume a2: "x \<notin> F"
    assume a3: "(\<And>i. i \<in> F \<Longrightarrow> f i + 0 \<le> g i + 0) \<Longrightarrow> sum_0 f F \<le> sum_0 g F"
    assume a4: "\<And>i. i \<in> insert x F \<Longrightarrow> f i + 0 \<le> g i + 0"
    obtain bb :: 'b where
      f5: "bb \<in> F \<and> \<not> f bb + 0 \<le> g bb + 0 \<or> sum_0 f F \<le> sum_0 g F"
      using a3 by blast
    have "\<forall>b. x \<noteq> b \<or> f b + 0 \<le> g b + 0"
      using a4 by simp
    then have "\<forall>a aa. f x + 0 + a \<le> g x + 0 + aa \<or> \<not> a \<le> aa"
      using add_mono by blast
    then show "sum_0 f (insert x F) \<le> sum_0 g (insert x F)"
      using f5 a4 a2 a1 by (metis (no_types) add_assoc insert_iff sum_0.insert sum_0.one_F)
  qed
qed

lemma (in ordered_ab_semigroup_add_0) sum_mono_0:
  "(\<And>i. i\<in>K \<Longrightarrow> f i + 0 \<le> g i) \<Longrightarrow> (\<Sum>i\<in>K. f i) \<le> (\<Sum>i\<in>K. g i)"
  apply (rule sum_mono_00)
  by (metis add_right_mono zero_neutral)

context ordered_ab_semigroup_add_0
begin

lemma sum_nonneg: "(\<And>x. x \<in> A \<Longrightarrow> 0 \<le> f x) \<Longrightarrow> 0 \<le> sum_0 f A"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x F)
  then have "0 + 0 \<le> f x + sum_0 f F" by (blast intro: add_mono)
  with insert show ?case by simp
qed

lemma sum_nonpos: "(\<And>x. x \<in> A \<Longrightarrow> f x \<le> 0) \<Longrightarrow> sum_0 f A \<le> 0"
proof (induct A rule: infinite_finite_induct)
  case infinite
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x F)
  then have "f x + sum_0 f F \<le> 0 + 0" by (blast intro: add_mono)
  with insert show ?case by simp
qed

lemma sum_mono2:
  assumes fin: "finite B"
    and sub: "A \<subseteq> B"
    and nn: "\<And>b. b \<in> B-A \<Longrightarrow> 0 \<le> f b"
  shows "sum_0 f A \<le> sum_0 f B"
proof -
  have "sum_0 f A \<le> sum_0 f A + sum_0 f (B-A)"
    by (metis add_left_mono sum_0.F_one nn sum_nonneg)
  also from fin finite_subset[OF sub fin] have "\<dots> = sum_0 f (A \<union> (B-A))"
    by (simp add: sum_0.union_disjoint del: Un_Diff_cancel)
  also from sub have "A \<union> (B-A) = B" by blast
  finally show ?thesis .
qed

lemma sum_le_included:
  assumes "finite s" "finite t"
  and "\<forall>y\<in>t. 0 \<le> g y" "(\<forall>x\<in>s. \<exists>y\<in>t. i y = x \<and> f x \<le> g y)"
  shows "sum_0 f s \<le> sum_0 g t"
proof -
  have "sum_0 f s \<le> sum_0 (\<lambda>y. sum_0 g {x. x\<in>t \<and> i x = y}) s"
  proof (rule sum_mono_0)
    fix y
    assume "y \<in> s"
    with assms obtain z where z: "z \<in> t" "y = i z" "f y \<le> g z" by auto
    hence "f y + 0 \<le> sum_0 g {z}"
      by (metis Diff_eq_empty_iff add_commute finite.simps add_left_mono sum_0.empty sum_0.insert_remove subset_insertI)
    also have "... \<le> sum_0 g {x \<in> t. i x = y}"
      apply (rule sum_mono2)
      using assms z by simp_all
    finally show "f y + 0 \<le> sum_0 g {x \<in> t. i x = y}" .
  qed
  also have "\<dots> \<le> sum_0 (\<lambda>y. sum_0 g {x. x\<in>t \<and> i x = y}) (i ` t)"
    using assms(2-4) by (auto intro!: sum_mono2 sum_nonneg)
  also have "\<dots> \<le> sum_0 g t"
    using assms by (auto simp: sum_image_gen_0[symmetric])
  finally show ?thesis .
qed

end

lemma sum_comp_morphism:
  "h 0 = 0 \<Longrightarrow> (\<And>x y. h (x + y) = h x + h y) \<Longrightarrow> sum_0 (h \<circ> g) A = h (sum_0 g A)"
  by (induct A rule: infinite_finite_induct) simp_all

lemma sum_cong_Suc:
  assumes "0 \<notin> A" "\<And>x. Suc x \<in> A \<Longrightarrow> f (Suc x) = g (Suc x)"
  shows "sum_0 f A = sum_0 g A"
proof (rule sum_0.cong)
  fix x
  assume "x \<in> A"
  with assms(1) show "f x = g x"
    by (cases x) (auto intro!: assms(2))
qed simp_all

end