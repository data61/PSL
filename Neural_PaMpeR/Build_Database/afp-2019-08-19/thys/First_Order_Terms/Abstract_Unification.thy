(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
subsection \<open>Abstract Unification\<close>

text \<open>We formalize an inference system for unification.\<close>

theory Abstract_Unification
  imports
    Unifiers
    Term_Pair_Multiset
    "Abstract-Rewriting.Abstract_Rewriting"
begin

(*TODO: move*)
lemma foldr_assoc:
  assumes "\<And>f g h. b (b f g) h = b f (b g h)"
  shows "foldr b xs (b y z) = b (foldr b xs y) z"
  using assms by (induct xs) simp_all

(*TODO: move*)
lemma union_commutes:
  "M + {#x#} + N = M + N + {#x#}"
  "M + mset xs + N = M + N + mset xs"
  by (auto simp: ac_simps)


subsubsection \<open>Inference Rules\<close>

text \<open>Inference rules with explicit substitutions.\<close>
inductive
  UNIF1 :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation multiset \<Rightarrow> ('f, 'v) equation multiset \<Rightarrow> bool"
where
  trivial [simp]: "UNIF1 Var (add_mset (t, t) E) E" |
  decomp: "\<lbrakk>length ss = length ts\<rbrakk> \<Longrightarrow>
    UNIF1 Var (add_mset (Fun f ss, Fun f ts) E) (E + mset (zip ss ts))" |
  Var_left: "\<lbrakk>x \<notin> vars_term t\<rbrakk> \<Longrightarrow>
    UNIF1 (subst x t) (add_mset (Var x, t) E) (subst_mset (subst x t) E)" |
  Var_right: "\<lbrakk>x \<notin> vars_term t\<rbrakk> \<Longrightarrow>
    UNIF1 (subst x t) (add_mset (t, Var x) E) (subst_mset (subst x t) E)"

text \<open>Relation version of @{const UNIF1} with implicit substitutions.\<close>
definition "unif = {(x, y). \<exists>\<sigma>. UNIF1 \<sigma> x y}"

lemma unif_UNIF1_conv:
  "(E, E') \<in> unif \<longleftrightarrow> (\<exists>\<sigma>. UNIF1 \<sigma> E E')"
  by (auto simp: unif_def)

lemma UNIF1_unifD:
  "UNIF1 \<sigma> E E' \<Longrightarrow> (E, E') \<in> unif"
  by (auto simp: unif_def)

text \<open>A termination order for @{const UNIF1}.\<close>
definition unifless :: "(('f, 'v) equation multiset \<times> ('f, 'v) equation multiset) set" where
  "unifless = inv_image (finite_psubset <*lex*> measure size_mset) (\<lambda>x. (vars_mset x, x))"

lemma wf_unifless:
  "wf unifless"
  by (auto simp: unifless_def)

lemma UNIF1_vars_mset_leq:
  assumes "UNIF1 \<sigma> E E'"
  shows "vars_mset E' \<subseteq> vars_mset E"
  using assms by (cases) (auto dest: mem_vars_mset_subst_mset)

lemma vars_mset_subset_size_mset_uniflessI [intro]:
  "vars_mset M \<subseteq> vars_mset N \<Longrightarrow> size_mset M < size_mset N \<Longrightarrow> (M, N) \<in> unifless"
  by (auto simp: unifless_def finite_vars_mset)

lemma vars_mset_psubset_uniflessI [intro]:
  "vars_mset M \<subset> vars_mset N \<Longrightarrow> (M, N) \<in> unifless"
  by (auto simp: unifless_def finite_vars_mset)

lemma UNIF1_unifless:
  assumes "UNIF1 \<sigma> E E'"
  shows "(E', E) \<in> unifless"
proof -
  have "vars_mset E' \<subseteq> vars_mset E"
    using UNIF1_vars_mset_leq [OF assms] .
  with assms
  show ?thesis
    apply cases
       apply (auto simp: pair_size_def intro!: Var_left_vars_mset_less Var_right_vars_mset_less)
    apply (rule vars_mset_subset_size_mset_uniflessI)
     apply auto
    using size_mset_Fun_less by fastforce
qed

lemma converse_unif_subset_unifless:
  "unif\<inverse> \<subseteq> unifless"
  using UNIF1_unifless by (auto simp: unif_def)


subsubsection \<open>Termination of the Inference Rules\<close>

lemma wf_converse_unif:
  "wf (unif\<inverse>)"
  by (rule wf_subset [OF wf_unifless converse_unif_subset_unifless])

text \<open>Reflexive and transitive closure of @{const UNIF1} collecting substitutions
produced by single steps.\<close>
inductive
  UNIF :: "('f, 'v) subst list \<Rightarrow> ('f, 'v) equation multiset \<Rightarrow> ('f, 'v) equation multiset \<Rightarrow> bool"
where
  empty [simp, intro!]: "UNIF [] E E" |
  step [intro]: "UNIF1 \<sigma> E E' \<Longrightarrow> UNIF ss E' E'' \<Longrightarrow> UNIF (\<sigma> # ss) E E''"

lemma unif_rtrancl_UNIF_conv:
  "(E, E') \<in> unif\<^sup>* \<longleftrightarrow> (\<exists>ss. UNIF ss E E')"
proof
  assume "(E, E') \<in> unif\<^sup>*"
  then show "\<exists>ss. UNIF ss E E'"
    by (induct rule: converse_rtrancl_induct) (auto simp: unif_UNIF1_conv)
next
  assume "\<exists>ss. UNIF ss E E'"
  then obtain ss where "UNIF ss E E'" ..
  then show "(E, E') \<in> unif\<^sup>*" by (induct) (auto dest: UNIF1_unifD)
qed

text \<open>Compose a list of substitutions.\<close>
definition compose :: "('f, 'v) subst list \<Rightarrow> ('f, 'v) subst"
  where
    "compose ss = List.foldr (\<circ>\<^sub>s) ss Var"

lemma compose_simps [simp]:
  "compose [] = Var"
  "compose (Var # ss) = compose ss"
  "compose (\<sigma> # ss) = \<sigma> \<circ>\<^sub>s compose ss"
  by (simp_all add: compose_def)

lemma compose_append [simp]:
  "compose (ss @ ts) = compose ss \<circ>\<^sub>s compose ts"
    using foldr_assoc [of "(\<circ>\<^sub>s)" ss Var "foldr (\<circ>\<^sub>s) ts Var"]
    by (simp add: compose_def ac_simps)

lemma set_mset_subst_mset [simp]:
  "set_mset (subst_mset \<sigma> E) = subst_set \<sigma> (set_mset E)"
  by (auto simp: subst_set_def subst_mset_def)

lemma UNIF1_subst_domain_Int:
  assumes "UNIF1 \<sigma> E E'"
  shows "subst_domain \<sigma> \<inter> vars_mset E' = {}"
  using assms by (cases) simp+

lemma UNIF1_subst_domain_subset:
  assumes "UNIF1 \<sigma> E E'"
  shows "subst_domain \<sigma> \<subseteq> vars_mset E"
  using assms by (cases) simp+

lemma UNIF_subst_domain_subset:
  assumes "UNIF ss E E'"
  shows "subst_domain (compose ss) \<subseteq> vars_mset E"
  using assms
  by (induct)
     (auto dest: UNIF1_subst_domain_subset UNIF1_vars_mset_leq simp: subst_domain_subst_compose)

lemma UNIF1_range_vars_subset:
  assumes "UNIF1 \<sigma> E E'"
  shows "range_vars \<sigma> \<subseteq> vars_mset E"
  using assms by (cases) (auto simp: range_vars_def)

lemma UNIF1_subst_domain_range_vars_Int:
  assumes "UNIF1 \<sigma> E E'"
  shows "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
  using assms by (cases) auto

lemma UNIF_range_vars_subset:
  assumes "UNIF ss E E'"
  shows "range_vars (compose ss) \<subseteq> vars_mset E"
  using assms
  by (induct)
     (auto dest: UNIF1_range_vars_subset UNIF1_vars_mset_leq
           dest!: range_vars_subst_compose_subset [THEN subsetD])

lemma UNIF_subst_domain_range_vars_Int:
  assumes "UNIF ss E E'"
  shows "subst_domain (compose ss) \<inter> range_vars (compose ss) = {}"
using assms
proof (induct)
  case (step \<sigma> E E' ss E'')
  from UNIF1_subst_domain_Int [OF step(1)]
    and UNIF_subst_domain_subset [OF step(2)]
    and UNIF1_subst_domain_range_vars_Int [OF step(1)]
    and UNIF_range_vars_subset [OF step(2)]
    have "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
      and "subst_domain (compose ss) \<inter> subst_domain \<sigma> = {}"
      and "subst_domain \<sigma> \<inter> range_vars (compose ss) = {}" by blast+
  then have "(subst_domain \<sigma> \<union> subst_domain (compose ss)) \<inter>
    ((range_vars \<sigma> - subst_domain (compose ss)) \<union> range_vars (compose ss)) = {}"
    using step(3) by auto
  then show ?case
    using subst_domain_subst_compose [of \<sigma> "compose ss"]
    and range_vars_subst_compose_subset [of \<sigma> "compose ss"]
    by (auto)
qed simp

text \<open>The inference rules generate idempotent substitutions.\<close>
lemma UNIF_idemp:
  assumes "UNIF ss E E'"
  shows "compose ss \<circ>\<^sub>s compose ss = compose ss"
  using UNIF_subst_domain_range_vars_Int [OF assms]
    by (simp only: subst_idemp_iff)

lemma UNIF1_mono:
  assumes "UNIF1 \<sigma> E E'"
  shows "UNIF1 \<sigma> (E + M) (E' + subst_mset \<sigma> M)"
  using assms
  by (cases) (auto intro: UNIF1.intros simp: union_commutes subst_mset_union [symmetric])

lemma unif_mono:
  assumes "(E, E') \<in> unif"
  shows "\<exists>\<sigma>. (E + M, E' + subst_mset \<sigma> M) \<in> unif"
  using assms by (auto simp: unif_UNIF1_conv intro: UNIF1_mono)

lemma unif_rtrancl_mono:
  assumes "(E, E') \<in> unif\<^sup>*"
  shows "\<exists>\<sigma>. (E + M, E' + subst_mset \<sigma> M) \<in> unif\<^sup>*"
using assms
proof (induction arbitrary: M rule: converse_rtrancl_induct)
  case base
  have "(E' + M, E' + subst_mset Var M) \<in> unif\<^sup>*" by auto
  then show ?case by blast
next
  case (step E F)
  obtain \<sigma> where "(E + M, F + subst_mset \<sigma> M) \<in> unif"
    using unif_mono [OF \<open>(E, F) \<in> unif\<close>] ..
  moreover obtain \<tau>
    where "(F + subst_mset \<sigma> M, E' + subst_mset \<tau> (subst_mset \<sigma> M)) \<in> unif\<^sup>*"
    using step.IH by blast
  ultimately have "(E + M, E' + subst_mset (\<sigma> \<circ>\<^sub>s \<tau>) M) \<in> unif\<^sup>*" by simp
  then show ?case by blast
qed


subsubsection \<open>Soundness of the Inference Rules\<close>

text \<open>The inference rules of unification are sound in the sense that
  when the empty set of equations is reached, a most general unifier
  is obtained.\<close>
lemma UNIF_empty_imp_is_mgu_compose:
  fixes E :: "('f, 'v) equation multiset"
  assumes "UNIF ss E {#}"
  shows "is_mgu (compose ss) (set_mset E)"
using assms
proof (induct ss E "{#}::('f, 'v) equation multiset")
  case (step \<sigma> E E' ss)
  then show ?case
    by (cases) (auto simp: is_mgu_subst_set_subst)
qed simp


subsubsection \<open>Completeness of the Inference Rules\<close>

lemma UNIF1_singleton_decomp [intro]:
  assumes "length ss = length ts"
  shows "UNIF1 Var {#(Fun f ss, Fun f ts)#} (mset (zip ss ts))"
  using UNIF1.decomp [OF assms, of f "{#}"] by simp

lemma UNIF1_singleton_Var_left [intro]:
  "x \<notin> vars_term t \<Longrightarrow> UNIF1 (subst x t) {#(Var x, t)#} {#}"
  using UNIF1.Var_left [of x t "{#}"] by simp

lemma UNIF1_singleton_Var_right [intro]:
  "x \<notin> vars_term t \<Longrightarrow> UNIF1 (subst x t) {#(t, Var x)#} {#}"
  using UNIF1.Var_right [of x t "{#}"] by simp

lemma not_UNIF1_singleton_Var_right [dest]:
  "\<not> UNIF1 Var {#(Var x, Var y)#} {#} \<Longrightarrow> x \<noteq> y"
  "\<not> UNIF1 (subst x (Var y)) {#(Var x, Var y)#} {#} \<Longrightarrow> x = y"
  by auto

lemma not_unifD:
  assumes "\<not> (\<exists>E'. ({#e#}, E') \<in> unif)"
  shows "(\<exists>x t. (e = (Var x, t) \<or> e = (t, Var x)) \<and> x \<in> vars_term t \<and> is_Fun t) \<or>
    (\<exists>f g ss ts. e = (Fun f ss, Fun g ts) \<and> (f \<noteq> g \<or> length ss \<noteq> length ts))"
proof (rule ccontr)
  assume *: "\<not> ?thesis"
  show False
  proof (cases e)
    case (Pair s t)
    with assms and * show ?thesis
      by (cases s) (cases t, auto simp: unif_def simp del: term.simps, (blast | succeed))+
  qed
qed

lemma unifiable_imp_unif:
  assumes "unifiable {e}"
  shows "\<exists>E'. ({#e#}, E') \<in> unif"
proof (rule ccontr)
  assume "\<not> ?thesis"
  from not_unifD [OF this] and assms
  show False by (auto simp: unifiable_def)
qed

lemma unifiable_imp_empty_or_unif:
  assumes "unifiable (set_mset E)"
  shows "E = {#} \<or> (\<exists>E'. (E, E') \<in> unif)"
proof (cases E)
  case [simp]: (add e E')
  from assms have "unifiable {e}" by (auto simp: unifiable_def unifiers_insert)
  from unifiable_imp_unif [OF this]
    obtain E'' where "({#e#}, E'') \<in> unif" ..
  then obtain \<sigma> where "UNIF1 \<sigma> {#e#} E''" by (auto simp: unif_UNIF1_conv)
  from UNIF1_mono [OF this] have "UNIF1 \<sigma> E (E'' + subst_mset \<sigma> E')" by (auto simp: ac_simps)
  then show ?thesis by (auto simp: unif_UNIF1_conv)
qed simp

lemma UNIF1_preserves_unifiers:
  assumes "UNIF1 \<sigma> E E'" and "\<tau> \<in> unifiers (set_mset E)"
  shows "(\<sigma> \<circ>\<^sub>s \<tau>) \<in> unifiers (set_mset E')"
  using assms by (cases) (auto simp: unifiers_def subst_mset_def)

lemma unif_preserves_unifiable:
  assumes "(E, E') \<in> unif" and "unifiable (set_mset E)"
  shows "unifiable (set_mset E')"
  using UNIF1_preserves_unifiers [of _ E E'] and assms
  by (auto simp: unif_UNIF1_conv unifiable_def)

lemma unif_imp_converse_unifless [dest]:
  "(x, y) \<in> unif \<Longrightarrow> (y, x) \<in> unifless"
  by (metis UNIF1_unifless unif_UNIF1_conv)

text \<open>Every unifiable set of equations can be reduced to the empty
  set by applying the inference rules of unification.\<close>

lemma unifiable_imp_empty:
  assumes "unifiable (set_mset E)"
  shows "(E, {#}) \<in> unif\<^sup>*"
  using assms
proof (induct E rule: wf_induct [OF wf_unifless])
  fix E :: "('f, 'v) equation multiset"
  presume IH: "\<And>E'. \<lbrakk>(E', E) \<in> unifless; unifiable (set_mset E')\<rbrakk> \<Longrightarrow>
    (E', {#}) \<in> unif\<^sup>*"
    and *: "unifiable (set_mset E)"
  show "(E, {#}) \<in> unif\<^sup>*"
  proof (cases "E = {#}")
    assume "E \<noteq> {#}"
    with unifiable_imp_empty_or_unif [OF *]
    obtain E' where "(E, E') \<in> unif" by auto
    with * have "(E', E) \<in> unifless" and "unifiable (set_mset E')"
      by (auto dest: unif_preserves_unifiable)
    from IH [OF this] and \<open>(E, E') \<in> unif\<close>
    show ?thesis by simp
  qed simp
qed simp

lemma unif_rtrancl_empty_imp_unifiable:
  assumes "(E, {#}) \<in> unif\<^sup>*"
  shows "unifiable (set_mset E)"
  using assms
  by (auto simp: unif_rtrancl_UNIF_conv unifiable_def is_mgu_def
           dest!: UNIF_empty_imp_is_mgu_compose)

lemma not_unifiable_imp_not_empty_NF:
  assumes "\<not> unifiable (set_mset E)"
  shows "\<exists>E'. E' \<noteq> {#} \<and> (E, E') \<in> unif\<^sup>!"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have *: "\<And>E'. (E, E') \<in> unif\<^sup>! \<Longrightarrow> E' = {#}" by auto
  have "SN unif" using wf_converse_unif by (auto simp: SN_iff_wf)
  then obtain E' where "(E, E') \<in> unif\<^sup>!"
    by (metis SN_imp_WN UNIV_I WN_onE)
  with * have "(E, {#}) \<in> unif\<^sup>*" by auto
  from unif_rtrancl_empty_imp_unifiable [OF this] and assms
  show False by contradiction
qed

lemma unif_rtrancl_preserves_unifiable:
  assumes "(E, E') \<in> unif\<^sup>*" and "unifiable (set_mset E)"
  shows "unifiable (set_mset E')"
  using assms by (induct) (auto simp: unif_preserves_unifiable)

text \<open>The inference rules for unification are complete in the
  sense that whenever it is not possible to reduce a set of equations
  @{term E} to the empty set, then @{term E} is not unifiable.\<close>

lemma empty_not_reachable_imp_not_unifiable:
  assumes "(E, {#}) \<notin> unif\<^sup>*"
  shows "\<not> unifiable (set_mset E)"
  using unifiable_imp_empty [of E] and assms by blast

text \<open>It is enough to reach an irreducible set of equations
  to conclude non-unifiability.\<close>
lemma irreducible_reachable_imp_not_unifiable:
  assumes "(E, E') \<in> unif\<^sup>!" and "E' \<noteq> {#}"
  shows "\<not> unifiable (set_mset E)"
proof -
  have "(E, E') \<in> unif\<^sup>*" and "(E', {#}) \<notin> unif\<^sup>*"
    using assms by (auto simp: NF_not_suc)
  moreover with empty_not_reachable_imp_not_unifiable
    have "\<not> unifiable (set_mset E')" by fast
  ultimately show ?thesis
    using unif_rtrancl_preserves_unifiable by fast
qed

end
