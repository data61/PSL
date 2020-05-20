(* Title: Misc_CryptHOL.thy
  Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Miscellaneous library additions\<close>

theory Misc_CryptHOL imports 
  Probabilistic_While.While_SPMF
  "HOL-Library.Rewrite"
  "HOL-Library.Simps_Case_Conv"
  "HOL-Library.Type_Length"
  "HOL-Eisbach.Eisbach"
  Coinductive.TLList
  Monad_Normalisation.Monad_Normalisation
  Monomorphic_Monad.Monomorphic_Monad
begin

hide_const (open) Henstock_Kurzweil_Integration.negligible

subsection \<open>HOL\<close>

lemma asm_rl_conv: "(PROP P \<Longrightarrow> PROP P) \<equiv> Trueprop True"
by(rule equal_intr_rule) iprover+

named_theorems if_distribs "Distributivity theorems for If"

lemma if_mono_cong: "\<lbrakk>b \<Longrightarrow> x \<le> x'; \<not> b \<Longrightarrow> y \<le> y' \<rbrakk> \<Longrightarrow> If b x y \<le> If b x' y'"
by simp

lemma if_cong_then: "\<lbrakk> b = b'; b' \<Longrightarrow> t = t'; e = e' \<rbrakk> \<Longrightarrow> If b t e = If b' t' e'"
by simp

lemma if_False_eq: "\<lbrakk> b \<Longrightarrow> False; e = e' \<rbrakk> \<Longrightarrow> If b t e = e'"
by auto

lemma imp_OO_imp [simp]: "(\<longrightarrow>) OO (\<longrightarrow>) = (\<longrightarrow>)"
by auto

lemma inj_on_fun_updD: "\<lbrakk> inj_on (f(x := y)) A; x \<notin> A \<rbrakk> \<Longrightarrow> inj_on f A"
by(auto simp add: inj_on_def split: if_split_asm)

lemma disjoint_notin1: "\<lbrakk> A \<inter> B = {}; x \<in> B \<rbrakk> \<Longrightarrow> x \<notin> A" by auto

lemma Least_le_Least:
  fixes x :: "'a :: wellorder"
  assumes "Q x"
  and Q: "\<And>x. Q x \<Longrightarrow> \<exists>y\<le>x. P y"
  shows "Least P \<le> Least Q"
proof -
  obtain f :: "'a \<Rightarrow> 'a" where "\<forall>a. \<not> Q a \<or> f a \<le> a \<and> P (f a)" using Q by moura
  moreover have "Q (Least Q)" using \<open>Q x\<close> by(rule LeastI)
  ultimately show ?thesis by (metis (full_types) le_cases le_less less_le_trans not_less_Least)
qed

subsection \<open>Relations\<close>

inductive Imagep :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool"
  for R P
where ImagepI: "\<lbrakk> P x; R x y \<rbrakk> \<Longrightarrow> Imagep R P y"

lemma r_r_into_tranclp: "\<lbrakk> r x y; r y z \<rbrakk> \<Longrightarrow> r^++ x z"
by(rule tranclp.trancl_into_trancl)(rule tranclp.r_into_trancl)

lemma transp_tranclp_id:
  assumes "transp R"
  shows "tranclp R = R"
proof(intro ext iffI)
  fix x y
  assume "R^++ x y"
  thus "R x y" by induction(blast dest: transpD[OF assms])+
qed simp

lemma transp_inv_image: "transp r \<Longrightarrow> transp (\<lambda>x y. r (f x) (f y))"
using trans_inv_image[where r="{(x, y). r x y}" and f = f]
by(simp add: transp_trans inv_image_def)

lemma Domainp_conversep: "Domainp R\<inverse>\<inverse> = Rangep R"
by(auto)

lemma bi_unique_rel_set_bij_betw:
  assumes unique: "bi_unique R"
  and rel: "rel_set R A B"
  shows "\<exists>f. bij_betw f A B \<and> (\<forall>x\<in>A. R x (f x))"
proof -
  from assms obtain f where f: "\<And>x. x \<in> A \<Longrightarrow> R x (f x)" and B: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
    apply(atomize_elim)
    apply(fold all_conj_distrib)
    apply(subst choice_iff[symmetric])
    apply(auto dest: rel_setD1)
    done
  have "inj_on f A" by(rule inj_onI)(auto dest!: f dest: bi_uniqueDl[OF unique])
  moreover have "f ` A = B" using rel
    by(auto 4 3 intro: B dest: rel_setD2 f bi_uniqueDr[OF unique])
  ultimately have "bij_betw f A B" unfolding bij_betw_def ..
  thus ?thesis using f by blast
qed

definition restrict_relp :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  ("_ \<upharpoonleft> (_ \<otimes> _)" [53, 54, 54] 53)
where "restrict_relp R P Q = (\<lambda>x y. R x y \<and> P x \<and> Q y)"

lemma restrict_relp_apply [simp]: "(R \<upharpoonleft> P \<otimes> Q) x y \<longleftrightarrow> R x y \<and> P x \<and> Q y"
by(simp add: restrict_relp_def)

lemma restrict_relpI [intro?]: "\<lbrakk> R x y; P x; Q y \<rbrakk> \<Longrightarrow> (R \<upharpoonleft> P \<otimes> Q) x y"
by(simp add: restrict_relp_def)

lemma restrict_relpE [elim?, cases pred]:
  assumes "(R \<upharpoonleft> P \<otimes> Q) x y"
  obtains (restrict_relp) "R x y" "P x" "Q y"
using assms by(simp add: restrict_relp_def)

lemma conversep_restrict_relp [simp]: "(R \<upharpoonleft> P \<otimes> Q)\<inverse>\<inverse> = R\<inverse>\<inverse> \<upharpoonleft> Q \<otimes> P"
by(auto simp add: fun_eq_iff)

lemma restrict_relp_restrict_relp [simp]: "R \<upharpoonleft> P \<otimes> Q \<upharpoonleft> P' \<otimes> Q' = R \<upharpoonleft> inf P P' \<otimes> inf Q Q'"
by(auto simp add: fun_eq_iff)

lemma restrict_relp_cong:
  "\<lbrakk> P = P'; Q = Q'; \<And>x y. \<lbrakk> P x; Q y \<rbrakk> \<Longrightarrow> R x y = R' x y \<rbrakk> \<Longrightarrow> R \<upharpoonleft> P \<otimes> Q = R' \<upharpoonleft> P' \<otimes> Q'"
by(auto simp add: fun_eq_iff)

lemma restrict_relp_cong_simp:
  "\<lbrakk> P = P'; Q = Q'; \<And>x y. P x =simp=> Q y =simp=> R x y = R' x y \<rbrakk> \<Longrightarrow> R \<upharpoonleft> P \<otimes> Q = R' \<upharpoonleft> P' \<otimes> Q'"
by(rule restrict_relp_cong; simp add: simp_implies_def)

lemma restrict_relp_parametric [transfer_rule]:
  includes lifting_syntax shows
  "((A ===> B ===> (=)) ===> (A ===> (=)) ===> (B ===> (=)) ===> A ===> B ===> (=)) restrict_relp restrict_relp"
unfolding restrict_relp_def[abs_def] by transfer_prover

lemma restrict_relp_mono: "\<lbrakk> R \<le> R'; P \<le> P'; Q \<le> Q' \<rbrakk> \<Longrightarrow> R \<upharpoonleft> P \<otimes> Q \<le> R' \<upharpoonleft> P' \<otimes> Q'"
by(simp add: le_fun_def)

lemma restrict_relp_mono': 
  "\<lbrakk> (R \<upharpoonleft> P \<otimes> Q) x y; \<lbrakk> R x y; P x; Q y \<rbrakk> \<Longrightarrow> R' x y &&& P' x &&& Q' y \<rbrakk>
  \<Longrightarrow> (R' \<upharpoonleft> P' \<otimes> Q') x y"
by(auto dest: conjunctionD1 conjunctionD2)

lemma restrict_relp_DomainpD: "Domainp (R \<upharpoonleft> P \<otimes> Q) x \<Longrightarrow> Domainp R x \<and> P x"
by(auto simp add: Domainp.simps)

lemma restrict_relp_True: "R \<upharpoonleft> (\<lambda>_. True) \<otimes> (\<lambda>_. True) = R"
by(simp add: fun_eq_iff)

lemma restrict_relp_False1: "R \<upharpoonleft> (\<lambda>_. False) \<otimes> Q = bot"
by(simp add: fun_eq_iff)

lemma restrict_relp_False2: "R \<upharpoonleft> P \<otimes> (\<lambda>_. False) = bot"
by(simp add: fun_eq_iff)

definition rel_prod2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('c \<times> 'b) \<Rightarrow> bool"
where "rel_prod2 R a = (\<lambda>(c, b). R a b)"

lemma rel_prod2_simps [simp]: "rel_prod2 R a (c, b) \<longleftrightarrow> R a b"
by(simp add: rel_prod2_def)

lemma restrict_rel_prod:
  "rel_prod (R \<upharpoonleft> I1 \<otimes> I2) (S \<upharpoonleft> I1' \<otimes> I2') = rel_prod R S \<upharpoonleft> pred_prod I1 I1' \<otimes> pred_prod I2 I2'"
by(auto simp add: fun_eq_iff)

lemma restrict_rel_prod1:
  "rel_prod (R \<upharpoonleft> I1 \<otimes> I2) S = rel_prod R S \<upharpoonleft> pred_prod I1 (\<lambda>_. True) \<otimes> pred_prod I2 (\<lambda>_. True)"
by(simp add: restrict_rel_prod[symmetric] restrict_relp_True)

lemma restrict_rel_prod2:
  "rel_prod R (S \<upharpoonleft> I1 \<otimes> I2) = rel_prod R S \<upharpoonleft> pred_prod (\<lambda>_. True) I1 \<otimes> pred_prod (\<lambda>_. True) I2"
by(simp add: restrict_rel_prod[symmetric] restrict_relp_True)

subsection \<open>Pairs\<close>

lemma split_apfst [simp]: "case_prod h (apfst f xy) = case_prod (h \<circ> f) xy"
by(cases xy) simp

definition corec_prod :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s \<Rightarrow> 'b) \<Rightarrow> 's \<Rightarrow> 'a \<times> 'b"
where "corec_prod f g = (\<lambda>s. (f s, g s))"

lemma corec_prod_apply: "corec_prod f g s = (f s, g s)"
by(simp add: corec_prod_def)

lemma corec_prod_sel [simp]:
  shows fst_corec_prod: "fst (corec_prod f g s) = f s"
  and snd_corec_prod: "snd (corec_prod f g s) = g s"
by(simp_all add: corec_prod_apply)

lemma apfst_corec_prod [simp]: "apfst h (corec_prod f g s) = corec_prod (h \<circ> f) g s"
by(simp add: corec_prod_apply)

lemma apsnd_corec_prod [simp]: "apsnd h (corec_prod f g s) = corec_prod f (h \<circ> g) s"
by(simp add: corec_prod_apply)

lemma map_corec_prod [simp]: "map_prod f g (corec_prod h k s) = corec_prod (f \<circ> h) (g \<circ> k) s"
by(simp add: corec_prod_apply)

lemma split_corec_prod [simp]: "case_prod h (corec_prod f g s) = h (f s) (g s)"
by(simp add: corec_prod_apply)

subsection \<open>Sums\<close>

lemma islE:
  assumes "isl x"
  obtains l where "x = Inl l"
using assms by(cases x) auto

lemma Inl_in_Plus [simp]: "Inl x \<in> A <+> B \<longleftrightarrow> x \<in> A"
by auto

lemma Inr_in_Plus [simp]: "Inr x \<in> A <+> B \<longleftrightarrow> x \<in> B"
by auto

lemma Inl_eq_map_sum_iff: "Inl x = map_sum f g y \<longleftrightarrow> (\<exists>z. y = Inl z \<and> x = f z)"
by(cases y) auto

lemma Inr_eq_map_sum_iff: "Inr x = map_sum f g y \<longleftrightarrow> (\<exists>z. y = Inr z \<and> x = g z)"
by(cases y) auto

subsection \<open>Option\<close>

declare is_none_bind [simp]

lemma case_option_collapse: "case_option x (\<lambda>_. x) y = x"
by(simp split: option.split)

lemma indicator_single_Some: "indicator {Some x} (Some y) = indicator {x} y"
by(simp split: split_indicator)

subsubsection \<open>Predicator and relator\<close>

lemma option_pred_mono_strong:
  "\<lbrakk> pred_option P x; \<And>a. \<lbrakk> a \<in> set_option x; P a \<rbrakk> \<Longrightarrow> P' a \<rbrakk> \<Longrightarrow> pred_option P' x"
by(fact option.pred_mono_strong)

lemma option_pred_map [simp]: "pred_option P (map_option f x) = pred_option (P \<circ> f) x"
by(fact option.pred_map)

lemma option_pred_o_map [simp]: "pred_option P \<circ> map_option f = pred_option (P \<circ> f)"
by(simp add: fun_eq_iff)

lemma option_pred_bind [simp]: "pred_option P (Option.bind x f) = pred_option (pred_option P \<circ> f) x"
by(simp add: pred_option_def)

lemma pred_option_conj [simp]:
  "pred_option (\<lambda>x. P x \<and> Q x) = (\<lambda>x. pred_option P x \<and> pred_option Q x)"
by(auto simp add: pred_option_def)

lemma pred_option_top [simp]:
  "pred_option (\<lambda>_. True) = (\<lambda>_. True)"
by(fact option.pred_True)

lemma rel_option_restrict_relpI [intro?]:
  "\<lbrakk> rel_option R x y; pred_option P x; pred_option Q y \<rbrakk> \<Longrightarrow> rel_option (R \<upharpoonleft> P \<otimes> Q) x y"
by(erule option.rel_mono_strong) simp

lemma rel_option_restrict_relpE [elim?]:
  assumes "rel_option (R \<upharpoonleft> P \<otimes> Q) x y"
  obtains "rel_option R x y" "pred_option P x" "pred_option Q y"
proof
  show "rel_option R x y" using assms by(auto elim!: option.rel_mono_strong)
  have "pred_option (Domainp (R \<upharpoonleft> P \<otimes> Q)) x" using assms by(fold option.Domainp_rel) blast
  then show "pred_option P x" by(rule option_pred_mono_strong)(blast dest!: restrict_relp_DomainpD)
  have "pred_option (Domainp (R \<upharpoonleft> P \<otimes> Q)\<inverse>\<inverse>) y" using assms
    by(fold option.Domainp_rel)(auto simp only: option.rel_conversep Domainp_conversep)
  then show "pred_option Q y" by(rule option_pred_mono_strong)(auto dest!: restrict_relp_DomainpD)
qed

lemma rel_option_restrict_relp_iff:
  "rel_option (R \<upharpoonleft> P \<otimes> Q) x y \<longleftrightarrow> rel_option R x y \<and> pred_option P x \<and> pred_option Q y"
by(blast intro: rel_option_restrict_relpI elim: rel_option_restrict_relpE)

lemma option_rel_map_restrict_relp:
  shows option_rel_map_restrict_relp1:
  "rel_option (R \<upharpoonleft> P \<otimes> Q) (map_option f x) = rel_option (R \<circ> f \<upharpoonleft> P \<circ> f \<otimes> Q) x"
  and option_rel_map_restrict_relp2:
  "rel_option (R \<upharpoonleft> P \<otimes> Q) x (map_option g y) = rel_option ((\<lambda>x. R x \<circ> g) \<upharpoonleft> P \<otimes> Q \<circ> g) x y"
by(simp_all add: option.rel_map restrict_relp_def fun_eq_iff)

subsubsection \<open>Orders on option\<close>

abbreviation le_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool"
where "le_option \<equiv> ord_option (=)"

lemma le_option_bind_mono:
  "\<lbrakk> le_option x y; \<And>a. a \<in> set_option x \<Longrightarrow> le_option (f a) (g a) \<rbrakk>
  \<Longrightarrow> le_option (Option.bind x f) (Option.bind y g)"
by(cases x) simp_all

lemma le_option_refl [simp]: "le_option x x"
by(cases x) simp_all


lemma le_option_conv_option_ord: "le_option = option_ord"
by(auto simp add: fun_eq_iff flat_ord_def elim: ord_option.cases)

definition pcr_Some :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b option \<Rightarrow> bool"
where "pcr_Some R x y \<longleftrightarrow> (\<exists>z. y = Some z \<and> R x z)"

lemma pcr_Some_simps [simp]: "pcr_Some R x (Some y) \<longleftrightarrow> R x y"
by(simp add: pcr_Some_def)

lemma pcr_SomeE [cases pred]:
  assumes "pcr_Some R x y"
  obtains (pcr_Some) z where "y = Some z" "R x z"
using assms by(auto simp add: pcr_Some_def)

subsubsection \<open>Filter for option\<close>

fun filter_option :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'a option"
where
  "filter_option P None = None"
| "filter_option P (Some x) = (if P x then Some x else None)"

lemma set_filter_option [simp]: "set_option (filter_option P x) = {y \<in> set_option x. P y}"
by(cases x) auto

lemma filter_map_option: "filter_option P (map_option f x) = map_option f (filter_option (P \<circ> f) x)"
by(cases x) simp_all

lemma is_none_filter_option [simp]: "Option.is_none (filter_option P x) \<longleftrightarrow> Option.is_none x \<or> \<not> P (the x)"
by(cases x) simp_all

lemma filter_option_eq_Some_iff [simp]: "filter_option P x = Some y \<longleftrightarrow> x = Some y \<and> P y"
by(cases x) auto

lemma Some_eq_filter_option_iff [simp]: "Some y = filter_option P x \<longleftrightarrow> x = Some y \<and> P y"
by(cases x) auto

lemma filter_conv_bind_option: "filter_option P x = Option.bind x (\<lambda>y. if P y then Some y else None)"
by(cases x) simp_all

subsubsection \<open>Assert for option\<close>

primrec assert_option :: "bool \<Rightarrow> unit option" where
  "assert_option True = Some ()"
| "assert_option False = None"

lemma set_assert_option_conv: "set_option (assert_option b) = (if b then {()} else {})"
by(simp)

lemma in_set_assert_option [simp]: "x \<in> set_option (assert_option b) \<longleftrightarrow> b"
by(cases b) simp_all


subsubsection \<open>Join on options\<close>

definition join_option :: "'a option option \<Rightarrow> 'a option"
where "join_option x = (case x of Some y \<Rightarrow> y | None \<Rightarrow> None)"

simps_of_case join_simps [simp, code]: join_option_def

lemma set_join_option [simp]: "set_option (join_option x) = \<Union>(set_option ` set_option x)"
by(cases x)(simp_all)

lemma in_set_join_option: "x \<in> set_option (join_option (Some (Some x)))"
by simp

lemma map_join_option: "map_option f (join_option x) = join_option (map_option (map_option f) x)"
by(cases x) simp_all

lemma bind_conv_join_option: "Option.bind x f = join_option (map_option f x)"
by(cases x) simp_all

lemma join_conv_bind_option: "join_option x = Option.bind x id"
by(cases x) simp_all

lemma join_option_parametric [transfer_rule]:
  includes lifting_syntax shows
  "(rel_option (rel_option R) ===> rel_option R) join_option join_option"
unfolding join_conv_bind_option[abs_def] by transfer_prover

lemma join_option_eq_Some [simp]: "join_option x = Some y \<longleftrightarrow> x = Some (Some y)"
by(cases x) simp_all

lemma Some_eq_join_option [simp]: "Some y = join_option x \<longleftrightarrow> x = Some (Some y)"
by(cases x) auto

lemma join_option_eq_None: "join_option x = None \<longleftrightarrow> x = None \<or> x = Some None"
by(cases x) simp_all

lemma None_eq_join_option: "None = join_option x \<longleftrightarrow> x = None \<or> x = Some None"
by(cases x) auto

subsubsection \<open>Zip on options\<close>

function zip_option :: "'a option \<Rightarrow> 'b option \<Rightarrow> ('a \<times> 'b) option"
where
  "zip_option (Some x) (Some y) = Some (x, y)"
| "zip_option _ None = None"
| "zip_option None _ = None"
by pat_completeness auto
termination by lexicographic_order

lemma zip_option_eq_Some_iff [iff]:
  "zip_option x y = Some (a, b) \<longleftrightarrow> x = Some a \<and> y = Some b"
by(cases "(x, y)" rule: zip_option.cases) simp_all

lemma set_zip_option [simp]:
  "set_option (zip_option x y) = set_option x \<times> set_option y"
by auto

lemma zip_map_option1: "zip_option (map_option f x) y = map_option (apfst f) (zip_option x y)"
by(cases "(x, y)" rule: zip_option.cases) simp_all

lemma zip_map_option2: "zip_option x (map_option g y) = map_option (apsnd g) (zip_option x y)"
by(cases "(x, y)" rule: zip_option.cases) simp_all

lemma map_zip_option:
  "map_option (map_prod f g) (zip_option x y) = zip_option (map_option f x) (map_option g y)"
by(simp add: zip_map_option1 zip_map_option2 option.map_comp apfst_def apsnd_def o_def prod.map_comp)

lemma zip_conv_bind_option:
  "zip_option x y = Option.bind x (\<lambda>x. Option.bind y (\<lambda>y. Some (x, y)))"
by(cases "(x, y)" rule: zip_option.cases) simp_all

lemma zip_option_parametric [transfer_rule]:
  includes lifting_syntax shows
  "(rel_option R ===> rel_option Q ===> rel_option (rel_prod R Q)) zip_option zip_option"
unfolding zip_conv_bind_option[abs_def] by transfer_prover

lemma rel_option_eqI [simp]: "rel_option (=) x x"
by(simp add: option.rel_eq)

subsubsection \<open>Binary supremum on @{typ "'a option"}\<close>

primrec sup_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option"
where
  "sup_option x None = x"
| "sup_option x (Some y) = (Some y)"

lemma sup_option_idem [simp]: "sup_option x x = x"
by(cases x) simp_all

lemma sup_option_assoc: "sup_option (sup_option x y) z = sup_option x (sup_option y z)"
by(cases z) simp_all

lemma sup_option_left_idem: "sup_option x (sup_option x y) = sup_option x y"
by(rewrite sup_option_assoc[symmetric])(simp)

lemmas sup_option_ai = sup_option_assoc sup_option_left_idem

lemma sup_option_None [simp]: "sup_option None y = y"
by(cases y) simp_all

subsubsection \<open>Maps\<close>

lemma map_add_apply: "(m1 ++ m2) x = sup_option (m1 x) (m2 x)"
by(simp add: map_add_def split: option.split)

lemma map_le_map_upd2: "\<lbrakk> f \<subseteq>\<^sub>m g; \<And>y'. f x = Some y' \<Longrightarrow> y' = y \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>m g(x \<mapsto> y)"
by(cases "x \<in> dom f")(auto simp add: map_le_def Ball_def)

lemma eq_None_iff_not_dom: "f x = None \<longleftrightarrow> x \<notin> dom f"
by auto

lemma card_ran_le_dom: "finite (dom m) \<Longrightarrow> card (ran m) \<le> card (dom m)"
by(simp add: ran_alt_def card_image_le)

lemma dom_subset_ran_iff:
  assumes "finite (ran m)"
  shows "dom m \<subseteq> ran m \<longleftrightarrow> dom m = ran m"
proof
  assume le: "dom m \<subseteq> ran m"
  then have "card (dom m) \<le> card (ran m)" by(simp add: card_mono assms)
  moreover have "card (ran m) \<le> card (dom m)" by(simp add: finite_subset[OF le assms] card_ran_le_dom)
  ultimately show "dom m = ran m" using card_subset_eq[OF assms le] by simp
qed simp

text \<open>
  We need a polymorphic constant for the empty map such that \<open>transfer_prover\<close>
  can use a custom transfer rule for @{const Map.empty}
\<close>
definition Map_empty where [simp]: "Map_empty \<equiv> Map.empty"

lemma map_le_Some1D: "\<lbrakk> m \<subseteq>\<^sub>m m'; m x = Some y \<rbrakk> \<Longrightarrow> m' x = Some y"
by(auto simp add: map_le_def Ball_def)

lemma map_le_fun_upd2: "\<lbrakk> f \<subseteq>\<^sub>m g; x \<notin> dom f \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>m g(x := y)"
by(auto simp add: map_le_def)

lemma map_eqI: "\<forall>x\<in>dom m \<union> dom m'. m x = m' x \<Longrightarrow> m = m'"
by(auto simp add: fun_eq_iff domIff intro: option.expand)


subsection \<open>Countable\<close>

lemma countable_lfp:
  assumes step: "\<And>Y. countable Y \<Longrightarrow> countable (F Y)"
  and cont: "Order_Continuity.sup_continuous F"
  shows "countable (lfp F)"
by(subst sup_continuous_lfp[OF cont])(simp add: countable_funpow[OF step])

lemma countable_lfp_apply:
  assumes step: "\<And>Y x. (\<And>x. countable (Y x)) \<Longrightarrow> countable (F Y x)"
  and cont: "Order_Continuity.sup_continuous F"
  shows "countable (lfp F x)"
proof -
  { fix n
    have "\<And>x. countable ((F ^^ n) bot x)"
      by(induct n)(auto intro: step) }
  thus ?thesis using cont by(simp add: sup_continuous_lfp)
qed


subsection \<open> Extended naturals \<close>

lemma idiff_enat_eq_enat_iff: "x - enat n = enat m \<longleftrightarrow> (\<exists>k. x = enat k \<and> k - n = m)"
  by (cases x) simp_all

lemma eSuc_SUP: "A \<noteq> {} \<Longrightarrow> eSuc (\<Squnion> (f ` A)) = (\<Squnion>x\<in>A. eSuc (f x))"
  by (subst eSuc_Sup) (simp_all add: image_comp)

lemma ereal_of_enat_1: "ereal_of_enat 1 = ereal 1"
  by (simp add: one_enat_def)

lemma ennreal_real_conv_ennreal_of_enat: "ennreal (real n) = ennreal_of_enat n"
  by (simp add: ennreal_of_nat_eq_real_of_nat)

lemma enat_add_sub_same2: "b \<noteq> \<infinity> \<Longrightarrow> a + b - b = (a :: enat)"
  by (cases a; cases b) simp_all

lemma enat_sub_add: "y \<le> x \<Longrightarrow> x - y + z = x + z - (y :: enat)"
  by (cases x; cases y; cases z) simp_all

lemma SUP_enat_eq_0_iff [simp]: "\<Squnion> (f ` A) = (0 :: enat) \<longleftrightarrow> (\<forall>x\<in>A. f x = 0)"
  by (simp add: bot_enat_def [symmetric])

lemma SUP_enat_add_left:
  assumes "I \<noteq> {}"
  shows "(SUP i\<in>I. f i + c :: enat) = (SUP i\<in>I. f i) + c" (is "?lhs = ?rhs")
proof(cases "c", rule antisym)
  case (enat n)
  show "?lhs \<le> ?rhs" by(auto 4 3 intro: SUP_upper intro: SUP_least)
  have "(SUP i\<in>I. f i) \<le> ?lhs - c" using enat 
    by(auto simp add: enat_add_sub_same2 intro!: SUP_least order_trans[OF _ SUP_upper[THEN enat_minus_mono1]])
  note add_right_mono[OF this, of c]
  also have "\<dots> + c \<le> ?lhs" using assms
    by(subst enat_sub_add)(auto intro: SUP_upper2 simp add: enat_add_sub_same2 enat)
  finally show "?rhs \<le> ?lhs" .
qed(simp add: assms SUP_constant)

lemma SUP_enat_add_right:
  assumes "I \<noteq> {}"
  shows "(SUP i\<in>I. c + f i :: enat) = c + (SUP i\<in>I. f i)"
using SUP_enat_add_left[OF assms, of f c]
by(simp add: add.commute)

lemma iadd_SUP_le_iff: "n + (SUP x\<in>A. f x :: enat) \<le> y \<longleftrightarrow> (if A = {} then n \<le> y else \<forall>x\<in>A. n + f x \<le> y)"
by(simp add: bot_enat_def SUP_enat_add_right[symmetric] SUP_le_iff)

lemma SUP_iadd_le_iff: "(SUP x\<in>A. f x :: enat) + n \<le> y \<longleftrightarrow> (if A = {} then n \<le> y else \<forall>x\<in>A. f x + n \<le> y)"
using iadd_SUP_le_iff[of n f A y] by(simp add: add.commute)


subsection \<open>Extended non-negative reals\<close>

lemma (in finite_measure) nn_integral_indicator_neq_infty: 
  "f -` A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+ x. indicator A (f x) \<partial>M) \<noteq> \<infinity>"
unfolding ennreal_indicator[symmetric]
apply(rule integrableD)
apply(rule integrable_const_bound[where B=1])
apply(simp_all add: indicator_vimage[symmetric])
done

lemma (in finite_measure) nn_integral_indicator_neq_top: 
  "f -` A \<in> sets M \<Longrightarrow> (\<integral>\<^sup>+ x. indicator A (f x) \<partial>M) \<noteq> \<top>"
by(drule nn_integral_indicator_neq_infty) simp

lemma nn_integral_indicator_map:
  assumes [measurable]: "f \<in> measurable M N" "{x\<in>space N. P x} \<in> sets N"
  shows "(\<integral>\<^sup>+x. indicator {x\<in>space N. P x} (f x) \<partial>M) = emeasure M {x\<in>space M. P (f x)}"
  using assms(1)[THEN measurable_space] 
  by (subst nn_integral_indicator[symmetric])
     (auto intro!: nn_integral_cong split: split_indicator simp del: nn_integral_indicator)


subsection \<open>BNF material\<close>

lemma transp_rel_fun: "\<lbrakk> is_equality Q; transp R \<rbrakk> \<Longrightarrow> transp (rel_fun Q R)"
by(rule transpI)(auto dest: transpD rel_funD simp add: is_equality_def)

lemma rel_fun_inf: "inf (rel_fun Q R) (rel_fun Q R') = rel_fun Q (inf R R')"
by(rule antisym)(auto elim: rel_fun_mono dest: rel_funD)

lemma reflp_fun1: includes lifting_syntax shows "\<lbrakk> is_equality A; reflp B \<rbrakk> \<Longrightarrow> reflp (A ===> B)"
by(simp add: reflp_def rel_fun_def is_equality_def)

lemma type_copy_id': "type_definition (\<lambda>x. x) (\<lambda>x. x) UNIV"
by unfold_locales simp_all

lemma type_copy_id: "type_definition id id UNIV"
by(simp add: id_def type_copy_id')

lemma GrpE [cases pred]:
  assumes "BNF_Def.Grp A f x y"
  obtains (Grp) "y = f x" "x \<in> A"
using assms
by(simp add: Grp_def)

lemma rel_fun_Grp_copy_Abs:
  includes lifting_syntax
  assumes "type_definition Rep Abs A"
  shows "rel_fun (BNF_Def.Grp A Abs) (BNF_Def.Grp B g) = BNF_Def.Grp {f. f ` A \<subseteq> B} (Rep ---> g)"
proof -
  interpret type_definition Rep Abs A by fact
  show ?thesis
    by(auto simp add: rel_fun_def Grp_def fun_eq_iff Abs_inverse Rep_inverse intro!: Rep)
qed

lemma rel_set_Grp:
  "rel_set (BNF_Def.Grp A f) = BNF_Def.Grp {B. B \<subseteq> A} (image f)"
by(auto simp add: rel_set_def BNF_Def.Grp_def fun_eq_iff)

lemma rel_set_comp_Grp:
  "rel_set R = (BNF_Def.Grp {x. x \<subseteq> {(x, y). R x y}} ((`) fst))\<inverse>\<inverse> OO BNF_Def.Grp {x. x \<subseteq> {(x, y). R x y}} ((`) snd)"
apply(auto 4 4 del: ext intro!: ext simp add: BNF_Def.Grp_def intro!: rel_setI intro: rev_bexI)
apply(simp add: relcompp_apply)
subgoal for A B
  apply(rule exI[where x="A \<times> B \<inter> {(x, y). R x y}"])
  apply(auto 4 3 dest: rel_setD1 rel_setD2 intro: rev_image_eqI)
  done
done

lemma Domainp_Grp: "Domainp (BNF_Def.Grp A f) = (\<lambda>x. x \<in> A)"
by(auto simp add: fun_eq_iff Grp_def)

lemma pred_prod_conj [simp]:
  shows pred_prod_conj1: "\<And>P Q R. pred_prod (\<lambda>x. P x \<and> Q x) R = (\<lambda>x. pred_prod P R x \<and> pred_prod Q R x)"
  and pred_prod_conj2: "\<And>P Q R. pred_prod P (\<lambda>x. Q x \<and> R x) = (\<lambda>x. pred_prod P Q x \<and> pred_prod P R x)"
by(auto simp add: pred_prod.simps)

lemma pred_sum_conj [simp]:
  shows pred_sum_conj1: "\<And>P Q R. pred_sum (\<lambda>x. P x \<and> Q x) R = (\<lambda>x. pred_sum P R x \<and> pred_sum Q R x)"
  and pred_sum_conj2: "\<And>P Q R. pred_sum P (\<lambda>x. Q x \<and> R x) = (\<lambda>x. pred_sum P Q x \<and> pred_sum P R x)"
by(auto simp add: pred_sum.simps fun_eq_iff)

lemma pred_list_conj [simp]: "list_all (\<lambda>x. P x \<and> Q x) = (\<lambda>x. list_all P x \<and> list_all Q x)"
by(auto simp add: list_all_def)

lemma pred_prod_top [simp]:
  "pred_prod (\<lambda>_. True) (\<lambda>_. True) = (\<lambda>_. True)"
by(simp add: pred_prod.simps fun_eq_iff)

lemma rel_fun_conversep: includes lifting_syntax shows
  "(A^--1 ===> B^--1) = (A ===> B)^--1"
by(auto simp add: rel_fun_def fun_eq_iff)

lemma left_unique_Grp [iff]:
  "left_unique (BNF_Def.Grp A f) \<longleftrightarrow> inj_on f A"
unfolding Grp_def left_unique_def by(auto simp add: inj_on_def)

lemma right_unique_Grp [simp, intro!]: "right_unique (BNF_Def.Grp A f)"
by(simp add: Grp_def right_unique_def)

lemma bi_unique_Grp [iff]:
  "bi_unique (BNF_Def.Grp A f) \<longleftrightarrow> inj_on f A"
by(simp add: bi_unique_alt_def)

lemma left_total_Grp [iff]:
  "left_total (BNF_Def.Grp A f) \<longleftrightarrow> A = UNIV"
by(auto simp add: left_total_def Grp_def)

lemma right_total_Grp [iff]:
  "right_total (BNF_Def.Grp A f) \<longleftrightarrow> f ` A = UNIV"
by(auto simp add: right_total_def BNF_Def.Grp_def image_def)

lemma bi_total_Grp [iff]:
  "bi_total (BNF_Def.Grp A f) \<longleftrightarrow> A = UNIV \<and> surj f"
by(auto simp add: bi_total_alt_def)

lemma left_unique_vimage2p [simp]:
  "\<lbrakk> left_unique P; inj f \<rbrakk> \<Longrightarrow> left_unique (BNF_Def.vimage2p f g P)"
unfolding vimage2p_Grp by(intro left_unique_OO) simp_all

lemma right_unique_vimage2p [simp]:
  "\<lbrakk> right_unique P; inj g \<rbrakk> \<Longrightarrow> right_unique (BNF_Def.vimage2p f g P)"
unfolding vimage2p_Grp by(intro right_unique_OO) simp_all

lemma bi_unique_vimage2p [simp]:
  "\<lbrakk> bi_unique P; inj f; inj g \<rbrakk> \<Longrightarrow> bi_unique (BNF_Def.vimage2p f g P)"
unfolding bi_unique_alt_def by simp

lemma left_total_vimage2p [simp]:
  "\<lbrakk> left_total P; surj g \<rbrakk> \<Longrightarrow> left_total (BNF_Def.vimage2p f g P)"
unfolding vimage2p_Grp by(intro left_total_OO) simp_all

lemma right_total_vimage2p [simp]:
  "\<lbrakk> right_total P; surj f \<rbrakk> \<Longrightarrow> right_total (BNF_Def.vimage2p f g P)"
unfolding vimage2p_Grp by(intro right_total_OO) simp_all

lemma bi_total_vimage2p [simp]:
  "\<lbrakk> bi_total P; surj f; surj g \<rbrakk> \<Longrightarrow> bi_total (BNF_Def.vimage2p f g P)"
unfolding bi_total_alt_def by simp

lemma vimage2p_eq [simp]:
  "inj f \<Longrightarrow> BNF_Def.vimage2p f f (=) = (=)"
by(auto simp add: vimage2p_def fun_eq_iff inj_on_def)

lemma vimage2p_conversep: "BNF_Def.vimage2p f g R^--1 = (BNF_Def.vimage2p g f R)^--1"
by(simp add: vimage2p_def fun_eq_iff)

subsection \<open>Transfer and lifting material\<close>

context includes lifting_syntax begin

lemma monotone_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A"
  shows "((A ===> A ===> (=)) ===> (B ===> B ===> (=)) ===> (A ===> B) ===> (=)) monotone monotone"
unfolding monotone_def[abs_def] by transfer_prover

lemma fun_ord_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total C"
  shows "((A ===> B ===> (=)) ===> (C ===> A) ===> (C ===> B) ===> (=)) fun_ord fun_ord"
unfolding fun_ord_def[abs_def] by transfer_prover

lemma Plus_parametric [transfer_rule]:
  "(rel_set A ===> rel_set B ===> rel_set (rel_sum A B)) (<+>) (<+>)"
unfolding Plus_def[abs_def] by transfer_prover

lemma pred_fun_parametric [transfer_rule]:
  assumes [transfer_rule]: "bi_total A"
  shows "((A ===> (=)) ===> (B ===> (=)) ===> (A ===> B) ===> (=)) pred_fun pred_fun"
unfolding pred_fun_def by(transfer_prover)

lemma rel_fun_eq_OO: "((=) ===> A) OO ((=) ===> B) = ((=) ===> A OO B)"
by(clarsimp simp add: rel_fun_def fun_eq_iff relcompp.simps) metis

end

lemma Quotient_set_rel_eq:
  includes lifting_syntax
  assumes "Quotient R Abs Rep T"
  shows "(rel_set T ===> rel_set T ===> (=)) (rel_set R) (=)"
proof(rule rel_funI iffI)+
  fix A B C D
  assume AB: "rel_set T A B" and CD: "rel_set T C D"
  have *: "\<And>x y. R x y = (T x (Abs x) \<and> T y (Abs y) \<and> Abs x = Abs y)"
    "\<And>a b. T a b \<Longrightarrow> Abs a = b"
    using assms unfolding Quotient_alt_def by simp_all

  { assume [simp]: "B = D"
    thus "rel_set R A C"
      by(auto 4 4 intro!: rel_setI dest: rel_setD1[OF AB, simplified] rel_setD2[OF AB, simplified] rel_setD2[OF CD] rel_setD1[OF CD] simp add: * elim!: rev_bexI)
  next
    assume AC: "rel_set R A C"
    show "B = D"
      apply safe
       apply(drule rel_setD2[OF AB], erule bexE)
       apply(drule rel_setD1[OF AC], erule bexE)
       apply(drule rel_setD1[OF CD], erule bexE)
       apply(simp add: *)
      apply(drule rel_setD2[OF CD], erule bexE)
      apply(drule rel_setD2[OF AC], erule bexE)
      apply(drule rel_setD1[OF AB], erule bexE)
      apply(simp add: *)
      done
  }
qed

lemma Domainp_eq: "Domainp (=) = (\<lambda>_. True)"
by(simp add: Domainp.simps fun_eq_iff)

lemma rel_fun_eq_onpI: "eq_onp (pred_fun P Q) f g \<Longrightarrow> rel_fun (eq_onp P) (eq_onp Q) f g"
by(auto simp add: eq_onp_def rel_fun_def)

lemma bi_unique_eq_onp: "bi_unique (eq_onp P)"
by(simp add: bi_unique_def eq_onp_def)

lemma rel_fun_eq_conversep: includes lifting_syntax shows "(A\<inverse>\<inverse> ===> (=)) = (A ===> (=))\<inverse>\<inverse>"
by(auto simp add: fun_eq_iff rel_fun_def)


subsection \<open>Arithmetic\<close>

lemma abs_diff_triangle_ineq2: "\<bar>a - b :: _ :: ordered_ab_group_add_abs\<bar> \<le> \<bar>a - c\<bar> + \<bar>c - b\<bar>"
by(rule order_trans[OF _ abs_diff_triangle_ineq]) simp

lemma (in ordered_ab_semigroup_add) add_left_mono_trans:
  "\<lbrakk> x \<le> a + b; b \<le> c \<rbrakk> \<Longrightarrow> x \<le> a + c"
by(erule order_trans)(rule add_left_mono)

lemma of_nat_le_one_cancel_iff [simp]:
  fixes n :: nat shows "real n \<le> 1 \<longleftrightarrow> n \<le> 1"
by linarith

lemma (in linordered_semidom) mult_right_le: "c \<le> 1 \<Longrightarrow> 0 \<le> a \<Longrightarrow> c * a \<le> a"
by(subst mult.commute)(rule mult_left_le)

subsection \<open>Chain-complete partial orders and \<open>partial_function\<close>\<close>

lemma fun_ordD: "fun_ord ord f g \<Longrightarrow> ord (f x) (g x)"
by(simp add: fun_ord_def)

lemma parallel_fixp_induct_strong:
  assumes ccpo1: "class.ccpo luba orda (mk_less orda)"
  and ccpo2: "class.ccpo lubb ordb (mk_less ordb)"
  and adm: "ccpo.admissible (prod_lub luba lubb) (rel_prod orda ordb) (\<lambda>x. P (fst x) (snd x))"
  and f: "monotone orda orda f"
  and g: "monotone ordb ordb g"
  and bot: "P (luba {}) (lubb {})"
  and step: "\<And>x y. \<lbrakk> orda x (ccpo.fixp luba orda f); ordb y (ccpo.fixp lubb ordb g); P x y \<rbrakk> \<Longrightarrow> P (f x) (g y)"
  shows "P (ccpo.fixp luba orda f) (ccpo.fixp lubb ordb g)"
proof -
  let ?P="\<lambda>x y. orda x (ccpo.fixp luba orda f) \<and> ordb y (ccpo.fixp lubb ordb g) \<and> P x y"
  show ?thesis using ccpo1 ccpo2 _ f g
  proof(rule parallel_fixp_induct[where P="?P", THEN conjunct2, THEN conjunct2])
    note [cont_intro] = 
      admissible_leI[OF ccpo1] ccpo.mcont_const[OF ccpo1]
      admissible_leI[OF ccpo2] ccpo.mcont_const[OF ccpo2]
    show "ccpo.admissible (prod_lub luba lubb) (rel_prod orda ordb) (\<lambda>xy. ?P (fst xy) (snd xy))"
      using adm by simp
    show "?P (luba {}) (lubb {})" using bot by(auto intro: ccpo.ccpo_Sup_least ccpo1 ccpo2 chain_empty)
    show "?P (f x) (g y)" if "?P x y" for x y using that
      apply(subst ccpo.fixp_unfold[OF ccpo1 f])
      apply(subst ccpo.fixp_unfold[OF ccpo2 g])
      apply(auto intro: step monotoneD[OF f] monotoneD[OF g])
      done
  qed
qed

lemma parallel_fixp_induct_strong_uc:
  assumes a: "partial_function_definitions orda luba"
  and b: "partial_function_definitions ordb lubb"
  and F: "\<And>x. monotone (fun_ord orda) orda (\<lambda>f. U1 (F (C1 f)) x)"
  and G: "\<And>y. monotone (fun_ord ordb) ordb (\<lambda>g. U2 (G (C2 g)) y)"
  and eq1: "f \<equiv> C1 (ccpo.fixp (fun_lub luba) (fun_ord orda) (\<lambda>f. U1 (F (C1 f))))"
  and eq2: "g \<equiv> C2 (ccpo.fixp (fun_lub lubb) (fun_ord ordb) (\<lambda>g. U2 (G (C2 g))))"
  and inverse: "\<And>f. U1 (C1 f) = f"
  and inverse2: "\<And>g. U2 (C2 g) = g"
  and adm: "ccpo.admissible (prod_lub (fun_lub luba) (fun_lub lubb)) (rel_prod (fun_ord orda) (fun_ord ordb)) (\<lambda>x. P (fst x) (snd x))"
  and bot: "P (\<lambda>_. luba {}) (\<lambda>_. lubb {})"
  and step: "\<And>f' g'. \<lbrakk> \<And>x. orda (U1 f' x) (U1 f x); \<And>y. ordb (U2 g' y) (U2 g y); P (U1 f') (U2 g') \<rbrakk> \<Longrightarrow> P (U1 (F f')) (U2 (G g'))"
  shows "P (U1 f) (U2 g)"
apply(unfold eq1 eq2 inverse inverse2)
apply(rule parallel_fixp_induct_strong[OF partial_function_definitions.ccpo[OF a] partial_function_definitions.ccpo[OF b] adm])
using F apply(simp add: monotone_def fun_ord_def)
using G apply(simp add: monotone_def fun_ord_def)
apply(simp add: fun_lub_def bot)
apply(rule step; simp add: inverse inverse2 eq1 eq2 fun_ordD)
done

lemmas parallel_fixp_induct_strong_1_1 = parallel_fixp_induct_strong_uc[
  of _ _ _ _ "\<lambda>x. x" _ "\<lambda>x. x" "\<lambda>x. x" _ "\<lambda>x. x",
  OF _ _ _ _ _ _ refl refl]

lemmas parallel_fixp_induct_strong_2_2 = parallel_fixp_induct_strong_uc[
  of _ _ _ _ "case_prod" _ "curry" "case_prod" _ "curry",
  where P="\<lambda>f g. P (curry f) (curry g)",
  unfolded case_prod_curry curry_case_prod curry_K,
  OF _ _ _ _ _ _ refl refl,
  split_format (complete), unfolded prod.case]
  for P

lemma fixp_induct_option': \<comment> \<open>Stronger induction rule\<close>
  fixes F :: "'c \<Rightarrow> 'c" and
    U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a option" and
    C :: "('b \<Rightarrow> 'a option) \<Rightarrow> 'c" and
    P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono: "\<And>x. mono_option (\<lambda>f. U (F (C f)) x)"
  assumes eq: "f \<equiv> C (ccpo.fixp (fun_lub (flat_lub None)) (fun_ord option_ord) (\<lambda>f. U (F (C f))))"
  assumes inverse2: "\<And>f. U (C f) = f"
  assumes step: "\<And>g x y. \<lbrakk> \<And>x y. U g x = Some y \<Longrightarrow> P x y; U (F g) x = Some y; \<And>x. option_ord (U g x) (U f x) \<rbrakk> \<Longrightarrow> P x y"
  assumes defined: "U f x = Some y"
  shows "P x y"
using step defined option.fixp_strong_induct_uc[of U F C, OF mono eq inverse2 option_admissible, of P]
unfolding fun_lub_def flat_lub_def fun_ord_def
by(simp (no_asm_use)) blast

declaration \<open>Partial_Function.init "option'" @{term option.fixp_fun}
  @{term option.mono_body} @{thm option.fixp_rule_uc} @{thm option.fixp_induct_uc}
  (SOME @{thm fixp_induct_option'})\<close>

lemma bot_fun_least [simp]: "(\<lambda>_. bot :: 'a :: order_bot) \<le> x"
by(fold bot_fun_def) simp

lemma fun_ord_conv_rel_fun: "fun_ord = rel_fun (=)"
by(simp add: fun_ord_def fun_eq_iff rel_fun_def)

inductive finite_chains :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  for ord
where finite_chainsI: "(\<And>Y. Complete_Partial_Order.chain ord Y \<Longrightarrow> finite Y) \<Longrightarrow> finite_chains ord"

lemma finite_chainsD: "\<lbrakk> finite_chains ord; Complete_Partial_Order.chain ord Y \<rbrakk> \<Longrightarrow> finite Y"
by(rule finite_chains.cases)

lemma finite_chains_flat_ord [simp, intro!]: "finite_chains (flat_ord x)"
proof
  fix Y
  assume chain: "Complete_Partial_Order.chain (flat_ord x) Y"
  show "finite Y"
  proof(cases "\<exists>y \<in> Y. y \<noteq> x")
    case True
    then obtain y where y: "y \<in> Y" and yx: "y \<noteq> x" by blast
    hence "Y \<subseteq> {x, y}" by(auto dest: chainD[OF chain] simp add: flat_ord_def)
    thus ?thesis by(rule finite_subset) simp
  next
    case False
    hence "Y \<subseteq> {x}" by auto
    thus ?thesis by(rule finite_subset) simp
  qed
qed    

lemma mcont_finite_chains:
  assumes finite: "finite_chains ord"
  and mono: "monotone ord ord' f"
  and ccpo: "class.ccpo lub ord (mk_less ord)"
  and ccpo': "class.ccpo lub' ord' (mk_less ord')"
  shows "mcont lub ord lub' ord' f"
proof(intro mcontI contI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ord Y" and Y: "Y \<noteq> {}"
  from finite chain have fin: "finite Y" by(rule finite_chainsD)
  from ccpo chain fin Y have lub: "lub Y \<in> Y" by(rule ccpo.in_chain_finite)

  interpret ccpo': ccpo lub' ord' "mk_less ord'" by(rule ccpo')

  have chain': "Complete_Partial_Order.chain ord' (f ` Y)" using chain
    by(rule chain_imageI)(rule monotoneD[OF mono])

  have "ord' (f (lub Y)) (lub' (f ` Y))" using chain'
    by(rule ccpo'.ccpo_Sup_upper)(simp add: lub)
  moreover
  have "ord' (lub' (f ` Y)) (f (lub Y))" using chain'
    by(rule ccpo'.ccpo_Sup_least)(blast intro: monotoneD[OF mono] ccpo.ccpo_Sup_upper[OF ccpo chain])
  ultimately show "f (lub Y) = lub' (f ` Y)" by(rule ccpo'.antisym)
qed(fact mono)  

lemma rel_fun_curry: includes lifting_syntax shows
  "(A ===> B ===> C) f g \<longleftrightarrow> (rel_prod A B ===> C) (case_prod f) (case_prod g)"
by(auto simp add: rel_fun_def)

lemma (in ccpo) Sup_image_mono:
  assumes ccpo: "class.ccpo luba orda lessa"
  and mono: "monotone orda (\<le>) f"
  and chain: "Complete_Partial_Order.chain orda A"
  and "A \<noteq> {}"
  shows "Sup (f ` A) \<le> (f (luba A))"
proof(rule ccpo_Sup_least)
  from chain show "Complete_Partial_Order.chain (\<le>) (f ` A)"
    by(rule chain_imageI)(rule monotoneD[OF mono])
  fix x
  assume "x \<in> f ` A"
  then obtain y where "x = f y" "y \<in> A" by blast
  from \<open>y \<in> A\<close> have "orda y (luba A)" by(rule ccpo.ccpo_Sup_upper[OF ccpo chain])
  hence "f y \<le> f (luba A)" by(rule monotoneD[OF mono])
  thus "x \<le> f (luba A)" using \<open>x = f y\<close> by simp
qed

lemma (in ccpo) admissible_le_mono:
  assumes "monotone (\<le>) (\<le>) f"
  shows "ccpo.admissible Sup (\<le>) (\<lambda>x. x \<le> f x)"
proof(rule ccpo.admissibleI)
  fix Y
  assume chain: "Complete_Partial_Order.chain (\<le>) Y"
    and Y: "Y \<noteq> {}"
    and le [rule_format]: "\<forall>x\<in>Y. x \<le> f x"
  have "\<Squnion>Y \<le> \<Squnion>(f ` Y)" using chain
    by(rule ccpo_Sup_least)(rule order_trans[OF le]; blast intro!: ccpo_Sup_upper chain_imageI[OF chain] intro: monotoneD[OF assms])
  also have "\<dots> \<le> f (\<Squnion>Y)"
    by(rule Sup_image_mono[OF _ assms chain Y, where lessa="(<)"]) unfold_locales
  finally show "\<Squnion>Y \<le> \<dots>" .
qed

lemma (in ccpo) fixp_induct_strong2:
  assumes adm: "ccpo.admissible Sup (\<le>) P"
  and mono: "monotone (\<le>) (\<le>) f"
  and bot: "P (\<Squnion>{})"
  and step: "\<And>x. \<lbrakk> x \<le> ccpo_class.fixp f; x \<le> f x; P x \<rbrakk> \<Longrightarrow> P (f x)"
  shows "P (ccpo_class.fixp f)"
proof(rule fixp_strong_induct[where P="\<lambda>x. x \<le> f x \<and> P x", THEN conjunct2])
  show "ccpo.admissible Sup (\<le>) (\<lambda>x. x \<le> f x \<and> P x)"
    using admissible_le_mono adm by(rule admissible_conj)(rule mono)
next
  show "\<Squnion>{} \<le> f (\<Squnion>{}) \<and> P (\<Squnion>{})"
    by(auto simp add: bot chain_empty intro: ccpo_Sup_least)
next
  fix x
  assume "x \<le> ccpo_class.fixp f" "x \<le> f x \<and> P x"
  thus "f x \<le> f (f x) \<and> P (f x)"
    by(auto dest: monotoneD[OF mono] intro: step)
qed(rule mono)

context partial_function_definitions begin

lemma fixp_induct_strong2_uc:
  fixes F :: "'c \<Rightarrow> 'c"
    and U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a"
    and C :: "('b \<Rightarrow> 'a) \<Rightarrow> 'c"
    and P :: "('b \<Rightarrow> 'a) \<Rightarrow> bool"
  assumes mono: "\<And>x. mono_body (\<lambda>f. U (F (C f)) x)"
    and eq: "f \<equiv> C (fixp_fun (\<lambda>f. U (F (C f))))"
    and inverse: "\<And>f. U (C f) = f"
    and adm: "ccpo.admissible lub_fun le_fun P"
    and bot: "P (\<lambda>_. lub {})"
    and step: "\<And>f'. \<lbrakk> le_fun (U f') (U f); le_fun (U f') (U (F f')); P (U f') \<rbrakk> \<Longrightarrow> P (U (F f'))"
  shows "P (U f)"
unfolding eq inverse
apply (rule ccpo.fixp_induct_strong2[OF ccpo adm])
apply (insert mono, auto simp: monotone_def fun_ord_def bot fun_lub_def)[2]
apply (rule_tac f'5="C x" in step)
apply (simp_all add: inverse eq)
done

end

lemmas parallel_fixp_induct_2_4 = parallel_fixp_induct_uc[
  of _ _ _ _ "case_prod" _ "curry" "\<lambda>f. case_prod (case_prod (case_prod f))" _ "\<lambda>f. curry (curry (curry f))",
  where P="\<lambda>f g. P (curry f) (curry (curry (curry g)))",
  unfolded case_prod_curry curry_case_prod curry_K,
  OF _ _ _ _ _ _ refl refl]
  for P
  
lemma (in ccpo) fixp_greatest:
  assumes f: "monotone (\<le>) (\<le>) f"
    and ge: "\<And>y. f y \<le> y \<Longrightarrow> x \<le> y"
  shows "x \<le> ccpo.fixp Sup (\<le>) f"
  by(rule ge)(simp add: fixp_unfold[OF f, symmetric])

lemma fixp_rolling:
  assumes "class.ccpo lub1 leq1 (mk_less leq1)"
    and "class.ccpo lub2 leq2 (mk_less leq2)"
    and f: "monotone leq1 leq2 f"
    and g: "monotone leq2 leq1 g"
  shows "ccpo.fixp lub1 leq1 (\<lambda>x. g (f x)) = g (ccpo.fixp lub2 leq2 (\<lambda>x. f (g x)))"
proof -
  interpret c1: ccpo lub1 leq1 "mk_less leq1" by fact
  interpret c2: ccpo lub2 leq2 "mk_less leq2" by fact
  show ?thesis
  proof(rule c1.antisym)
    have fg: "monotone leq2 leq2 (\<lambda>x. f (g x))" using f g by(rule monotone2monotone) simp_all
    have gf: "monotone leq1 leq1 (\<lambda>x. g (f x))" using g f by(rule monotone2monotone) simp_all
    show "leq1 (c1.fixp (\<lambda>x. g (f x))) (g (c2.fixp (\<lambda>x. f (g x))))" using gf
      by(rule c1.fixp_lowerbound)(subst (2) c2.fixp_unfold[OF fg], simp)
    show "leq1 (g (c2.fixp (\<lambda>x. f (g x)))) (c1.fixp (\<lambda>x. g (f x)))" using gf
    proof(rule c1.fixp_greatest)
      fix u
      assume u: "leq1 (g (f u)) u"
      have "leq1 (g (c2.fixp (\<lambda>x. f (g x)))) (g (f u))"
        by(intro monotoneD[OF g] c2.fixp_lowerbound[OF fg] monotoneD[OF f u])
      then show "leq1 (g (c2.fixp (\<lambda>x. f (g x)))) u" using u by(rule c1.order_trans)
    qed
  qed
qed

lemma fixp_lfp_parametric_eq:
  includes lifting_syntax
  assumes f: "\<And>x. lfp.mono_body (\<lambda>f. F f x)"
  and g: "\<And>x. lfp.mono_body (\<lambda>f. G f x)"
  and param: "((A ===> (=)) ===> A ===> (=)) F G"
  shows "(A ===> (=)) (lfp.fixp_fun F) (lfp.fixp_fun G)"
using f g
proof(rule parallel_fixp_induct_1_1[OF complete_lattice_partial_function_definitions complete_lattice_partial_function_definitions _ _ reflexive reflexive, where P="(A ===> (=))"])
  show "ccpo.admissible (prod_lub lfp.lub_fun lfp.lub_fun) (rel_prod lfp.le_fun lfp.le_fun) (\<lambda>x. (A ===> (=)) (fst x) (snd x))"
    unfolding rel_fun_def by simp
  show "(A ===> (=)) (\<lambda>_. \<Squnion>{}) (\<lambda>_. \<Squnion>{})" by auto
  show "(A ===> (=)) (F f) (G g)" if "(A ===> (=)) f g" for f g
    using that by(rule rel_funD[OF param])
qed

lemma mono2mono_map_option[THEN option.mono2mono, simp, cont_intro]:
  shows monotone_map_option: "monotone option_ord option_ord (map_option f)"
by(rule monotoneI)(auto simp add: flat_ord_def)

lemma mcont2mcont_map_option[THEN option.mcont2mcont, simp, cont_intro]:
  shows mcont_map_option: "mcont (flat_lub None) option_ord (flat_lub None) option_ord (map_option f)"
by(rule mcont_finite_chains[OF _ _ flat_interpretation[THEN ccpo] flat_interpretation[THEN ccpo]]) simp_all

lemma mono2mono_set_option [THEN lfp.mono2mono]:
  shows monotone_set_option: "monotone option_ord (\<subseteq>) set_option"
by(auto intro!: monotoneI simp add: option_ord_Some1_iff)

lemma mcont2mcont_set_option [THEN lfp.mcont2mcont, cont_intro, simp]:
  shows mcont_set_option: "mcont (flat_lub None) option_ord Union (\<subseteq>) set_option"
by(rule mcont_finite_chains)(simp_all add: monotone_set_option ccpo option.partial_function_definitions_axioms)

lemma eadd_gfp_partial_function_mono [partial_function_mono]:
  "\<lbrakk> monotone (fun_ord (\<ge>)) (\<ge>) f; monotone (fun_ord (\<ge>)) (\<ge>) g \<rbrakk>
  \<Longrightarrow> monotone (fun_ord (\<ge>)) (\<ge>) (\<lambda>x. f x + g x :: enat)"
by(rule mono2mono_gfp_eadd)

lemma map_option_mono [partial_function_mono]:
  "mono_option B \<Longrightarrow> mono_option (\<lambda>f. map_option g (B f))"
unfolding map_conv_bind_option by(rule bind_mono) simp_all


subsection \<open>Folding over finite sets\<close>

lemma (in comp_fun_commute) fold_invariant_remove [consumes 1, case_names start step]:
  assumes fin: "finite A"
  and start: "I A s"
  and step: "\<And>x s A'. \<lbrakk> x \<in> A'; I A' s; A' \<subseteq> A \<rbrakk> \<Longrightarrow> I (A' - {x}) (f x s)"
  shows "I {} (Finite_Set.fold f s A)"
proof -
  define A' where "A' == A"
  with fin start have "finite A'" "A' \<subseteq> A" "I A' s" by simp_all
  thus "I {} (Finite_Set.fold f s A')"
  proof(induction arbitrary: s)
    case empty thus ?case by simp
  next
    case (insert x A')
    let ?A' = "insert x A'"
    have "x \<in> ?A'" "I ?A' s" "?A' \<subseteq> A" using insert by auto
    hence "I (?A' - {x}) (f x s)" by(rule step)
    with insert have "A' \<subseteq> A" "I A' (f x s)" by auto
    hence "I {} (Finite_Set.fold f (f x s) A')" by(rule insert.IH)
    thus ?case using insert by(simp add: fold_insert2 del: fold_insert)
  qed
qed

lemma (in comp_fun_commute) fold_invariant_insert [consumes 1, case_names start step]:
  assumes fin: "finite A"
  and start: "I {} s"
  and step: "\<And>x s A'. \<lbrakk> I A' s; x \<notin> A'; x \<in> A; A' \<subseteq> A \<rbrakk> \<Longrightarrow> I (insert x A') (f x s)"
  shows "I A (Finite_Set.fold f s A)"
using fin start
proof(rule fold_invariant_remove[where I="\<lambda>A'. I (A - A')" and A=A and s=s, simplified])
  fix x s A'
  assume *: "x \<in> A'" "I (A - A') s" "A' \<subseteq> A"
  hence "x \<notin> A - A'" "x \<in> A" "A - A' \<subseteq> A" by auto
  with \<open>I (A - A') s\<close> have "I (insert x (A - A')) (f x s)" by(rule step)
  also have "insert x (A - A') = A - (A' - {x})" using * by auto
  finally show "I \<dots> (f x s)" .
qed

lemma (in comp_fun_idem) fold_set_union:
  assumes "finite A" "finite B"
  shows "Finite_Set.fold f z (A \<union> B) = Finite_Set.fold f (Finite_Set.fold f z A) B"
using assms(2,1) by induction simp_all


subsection \<open>Parametrisation of transfer rules\<close>

attribute_setup transfer_parametric = \<open> 
  Attrib.thm >> (fn parametricity =>
    Thm.rule_attribute [] (fn context => fn transfer_rule =>
      let
        val ctxt = Context.proof_of context;
        val thm' = Lifting_Term.parametrize_transfer_rule ctxt transfer_rule
      in Lifting_Def.generate_parametric_transfer_rule ctxt thm' parametricity
      end
      handle Lifting_Term.MERGE_TRANSFER_REL msg => error (Pretty.string_of msg)
      ))
\<close> "combine transfer rule with parametricity theorem"

subsection \<open>Lists\<close>

lemma nth_eq_tlI: "xs ! n = z \<Longrightarrow> (x # xs) ! Suc n = z"
by simp

lemma list_all2_append':
  "length us = length vs \<Longrightarrow> list_all2 P (xs @ us) (ys @ vs) \<longleftrightarrow> list_all2 P xs ys \<and> list_all2 P us vs"
by(auto simp add: list_all2_append1 list_all2_append2 dest: list_all2_lengthD)

definition disjointp :: "('a \<Rightarrow> bool) list \<Rightarrow> bool"
where "disjointp xs = disjoint_family_on (\<lambda>n. {x. (xs ! n) x}) {0..<length xs}"

lemma disjointpD:
  "\<lbrakk> disjointp xs; (xs ! n) x; (xs ! m) x; n < length xs; m < length xs \<rbrakk> \<Longrightarrow> n = m"
by(auto 4 3 simp add: disjointp_def disjoint_family_on_def)

lemma disjointpD':
  "\<lbrakk> disjointp xs; P x; Q x; xs ! n = P; xs ! m = Q; n < length xs; m < length xs \<rbrakk> \<Longrightarrow> n = m"
by(auto 4 3 simp add: disjointp_def disjoint_family_on_def)

subsubsection \<open>List of a given length\<close>

inductive_set nlists :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set" for A n
where nlists: "\<lbrakk> set xs \<subseteq> A; length xs = n \<rbrakk> \<Longrightarrow> xs \<in> nlists A n"
hide_fact (open) nlists

lemma nlists_alt_def: "nlists A n = {xs. set xs \<subseteq> A \<and> length xs = n}"
by(auto simp add: nlists.simps)

lemma nlists_empty: "nlists {} n = (if n = 0 then {[]} else {})"
by(auto simp add: nlists_alt_def)

lemma nlists_empty_gt0 [simp]: "n > 0 \<Longrightarrow> nlists {} n = {}"
by(simp add: nlists_empty)

lemma nlists_0 [simp]: "nlists A 0 = {[]}"
by(auto simp add: nlists_alt_def)

lemma Cons_in_nlists_Suc [simp]: "x # xs \<in> nlists A (Suc n) \<longleftrightarrow> x \<in> A \<and> xs \<in> nlists A n"
by(simp add: nlists_alt_def)

lemma Nil_in_nlists [simp]: "[] \<in> nlists A n \<longleftrightarrow> n = 0"
by(auto simp add: nlists_alt_def)

lemma Cons_in_nlists_iff: "x # xs \<in> nlists A n \<longleftrightarrow> (\<exists>n'. n = Suc n' \<and> x \<in> A \<and> xs \<in> nlists A n')"
by(cases n) simp_all

lemma in_nlists_Suc_iff: "xs \<in> nlists A (Suc n) \<longleftrightarrow> (\<exists>x xs'. xs = x # xs' \<and> x \<in> A \<and> xs' \<in> nlists A n)"
by(cases xs) simp_all

lemma nlists_Suc: "nlists A (Suc n) = (\<Union>x\<in>A. (#) x ` nlists A n)"
by(auto 4 3 simp add: in_nlists_Suc_iff intro: rev_image_eqI)

lemma replicate_in_nlists [simp, intro]: "x \<in> A \<Longrightarrow> replicate n x \<in> nlists A n"
by(simp add: nlists_alt_def set_replicate_conv_if)

lemma nlists_eq_empty_iff [simp]: "nlists A n = {} \<longleftrightarrow> n > 0 \<and> A = {}"
using replicate_in_nlists by(cases n)(auto)

lemma finite_nlists [simp]: "finite A \<Longrightarrow> finite (nlists A n)"
by(induction n)(simp_all add: nlists_Suc)

lemma finite_nlistsD: 
  assumes "finite (nlists A n)"
  shows "finite A \<or> n = 0"
proof(rule disjCI)
  assume "n \<noteq> 0"
  then obtain n' where n: "n = Suc n'" by(cases n)auto
  then have "A = hd ` nlists A n" by(auto 4 4 simp add: nlists_Suc intro: rev_image_eqI rev_bexI)
  also have "finite \<dots>" using assms ..
  finally show "finite A" .
qed

lemma finite_nlists_iff: "finite (nlists A n) \<longleftrightarrow> finite A \<or> n = 0"
by(auto dest: finite_nlistsD)

lemma card_nlists: "card (nlists A n) = card A ^ n"
proof(induction n)
  case (Suc n)
  have "card (\<Union>x\<in>A. (#) x ` nlists A n) = card A * card (nlists A n)"
  proof(cases "finite A")
    case True
    then show ?thesis by(subst card_UN_disjoint)(auto simp add: card_image inj_on_def)
  next
    case False
    hence "\<not> finite (\<Union>x\<in>A. (#) x ` nlists A n)"
      unfolding nlists_Suc[symmetric] by(auto dest: finite_nlistsD)
    then show ?thesis using False by simp
  qed
  then show ?case using Suc.IH by(simp add: nlists_Suc)
qed simp

lemma in_nlists_UNIV: "xs \<in> nlists UNIV n \<longleftrightarrow> length xs = n"
by(simp add: nlists_alt_def)

subsubsection \<open> The type of lists of a given length \<close>

typedef (overloaded) ('a, 'b :: len0) nlist = "nlists (UNIV :: 'a set) (LENGTH('b))"
proof
  show "replicate LENGTH('b) undefined \<in> ?nlist" by simp
qed

setup_lifting type_definition_nlist

subsection \<open>Streams and infinite lists\<close>

primrec sprefix :: "'a list \<Rightarrow> 'a stream \<Rightarrow> bool" where
  sprefix_Nil: "sprefix [] ys = True"
| sprefix_Cons: "sprefix (x # xs) ys \<longleftrightarrow> x = shd ys \<and> sprefix xs (stl ys)"

lemma sprefix_append: "sprefix (xs @ ys) zs \<longleftrightarrow> sprefix xs zs \<and> sprefix ys (sdrop (length xs) zs)"
by(induct xs arbitrary: zs) simp_all

lemma sprefix_stake_same [simp]: "sprefix (stake n xs) xs"
by(induct n arbitrary: xs) simp_all

lemma sprefix_same_imp_eq:
  assumes "sprefix xs ys" "sprefix xs' ys"
  and "length xs = length xs'"
  shows "xs = xs'"
using assms(3,1,2) by(induct arbitrary: ys rule: list_induct2) auto

lemma sprefix_shift_same [simp]:
  "sprefix xs (xs @- ys)"
by(induct xs) simp_all

lemma sprefix_shift [simp]:
  "length xs \<le> length ys \<Longrightarrow> sprefix xs (ys @- zs) \<longleftrightarrow> prefix xs ys"
by(induct xs arbitrary: ys)(simp, case_tac ys, auto)

lemma prefixeq_stake2 [simp]: "prefix xs (stake n ys) \<longleftrightarrow> length xs \<le> n \<and> sprefix xs ys"
proof(induct xs arbitrary: n ys)
  case (Cons x xs)
  thus ?case by(cases ys n rule: stream.exhaust[case_product nat.exhaust]) auto
qed simp

lemma tlength_eq_infinity_iff: "tlength xs = \<infinity> \<longleftrightarrow> \<not> tfinite xs"
including tllist.lifting by transfer(simp add: llength_eq_infty_conv_lfinite)

subsection \<open>Monomorphic monads\<close>

context includes lifting_syntax begin
local_setup \<open>Local_Theory.map_background_naming (Name_Space.mandatory_path "monad")\<close>

definition bind_option :: "'m fail \<Rightarrow> 'a option \<Rightarrow> ('a \<Rightarrow> 'm) \<Rightarrow> 'm"
where "bind_option fail x f = (case x of None \<Rightarrow> fail | Some x' \<Rightarrow> f x')" for fail

simps_of_case bind_option_simps [simp]: bind_option_def

lemma bind_option_parametric [transfer_rule]:
  "(M ===> rel_option B ===> (B ===> M) ===> M) bind_option bind_option"
unfolding bind_option_def by transfer_prover

lemma bind_option_K:
  "\<And>monad. (x = None \<Longrightarrow> m = fail) \<Longrightarrow> bind_option fail x (\<lambda>_. m) = m"
by(cases x) simp_all

end

lemma bind_option_option [simp]: "monad.bind_option None = Option.bind"
by(simp add: monad.bind_option_def fun_eq_iff split: option.split)

context monad_fail_hom begin

lemma hom_bind_option: "h (monad.bind_option fail1 x f) = monad.bind_option fail2 x (h \<circ> f)"
by(cases x)(simp_all)

end

lemma bind_option_set [simp]: "monad.bind_option fail_set = (\<lambda>x f. \<Union> (f ` set_option x))"
by(simp add: monad.bind_option_def fun_eq_iff split: option.split)

lemma run_bind_option_stateT [simp]:
  "\<And>more. run_state (monad.bind_option (fail_state fail) x f) s = 
  monad.bind_option fail x (\<lambda>y. run_state (f y) s)"
by(cases x) simp_all

lemma run_bind_option_envT [simp]:
  "\<And>more. run_env (monad.bind_option (fail_env fail) x f) s = 
  monad.bind_option fail x (\<lambda>y. run_env (f y) s)"
by(cases x) simp_all


subsection \<open>Measures\<close>

declare sets_restrict_space_count_space [measurable_cong]

lemma (in sigma_algebra) sets_Collect_countable_Ex1:
  "(\<And>i :: 'i :: countable. {x \<in> \<Omega>. P i x} \<in> M) \<Longrightarrow> {x \<in> \<Omega>. \<exists>!i. P i x} \<in> M"
using sets_Collect_countable_Ex1'[of "UNIV :: 'i set"] by simp

lemma pred_countable_Ex1 [measurable]:
  "(\<And>i :: _ :: countable. Measurable.pred M (\<lambda>x. P i x))
  \<Longrightarrow> Measurable.pred M (\<lambda>x. \<exists>!i. P i x)"
unfolding pred_def by(rule sets.sets_Collect_countable_Ex1)

lemma measurable_snd_count_space [measurable]: 
  "A \<subseteq> B \<Longrightarrow> snd \<in> measurable (M1 \<Otimes>\<^sub>M count_space A) (count_space B)"
by(auto simp add: measurable_def space_pair_measure snd_vimage_eq_Times Times_Int_Times)

subsection \<open>Sequence space\<close>

lemma (in sequence_space) nn_integral_split:
  assumes f[measurable]: "f \<in> borel_measurable S"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>S) = (\<integral>\<^sup>+\<omega>. (\<integral>\<^sup>+\<omega>'. f (comb_seq i \<omega> \<omega>') \<partial>S) \<partial>S)"
by (subst PiM_comb_seq[symmetric, where i=i])
   (simp add: nn_integral_distr P.nn_integral_fst[symmetric])

lemma (in sequence_space) prob_Collect_split:
  assumes f[measurable]: "{x\<in>space S. P x} \<in> sets S"
  shows "\<P>(x in S. P x) = (\<integral>\<^sup>+x. \<P>(x' in S. P (comb_seq i x x')) \<partial>S)"
proof -
  have "\<P>(x in S. P x) = (\<integral>\<^sup>+x. (\<integral>\<^sup>+x'. indicator {x\<in>space S. P x} (comb_seq i x x') \<partial>S) \<partial>S)"
    using nn_integral_split[of "indicator {x\<in>space S. P x}"] by (auto simp: emeasure_eq_measure)
  also have "\<dots> = (\<integral>\<^sup>+x. \<P>(x' in S. P (comb_seq i x x')) \<partial>S)"
    by (intro nn_integral_cong) (auto simp: emeasure_eq_measure nn_integral_indicator_map)
  finally show ?thesis .
qed

subsection \<open>Probability mass functions\<close>

lemma measure_map_pmf_conv_distr:
  "measure_pmf (map_pmf f p) = distr (measure_pmf p) (count_space UNIV) f"
by(fact map_pmf_rep_eq)

abbreviation coin_pmf :: "bool pmf" where "coin_pmf \<equiv> pmf_of_set UNIV"

text \<open>The rule @{thm [source] rel_pmf_bindI} is not complete as a program logic.\<close>
notepad begin
  define x where "x = pmf_of_set {True, False}"
  define y where "y = pmf_of_set {True, False}"
  define f where "f x = pmf_of_set {True, False}" for x :: bool
  define g :: "bool \<Rightarrow> bool pmf" where "g = return_pmf"
  define P :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "P = (=)"
  have "rel_pmf P (bind_pmf x f) (bind_pmf y g)"
    by(simp add: P_def f_def[abs_def] g_def y_def bind_return_pmf' pmf.rel_eq)
  have "\<not> R x y" if "\<And>x y. R x y \<Longrightarrow> rel_pmf P (f x) (g y)" for R x y
    \<comment> \<open>Only the empty relation satisfies @{thm [source] rel_pmf_bindI}'s second premise.\<close>
  proof
    assume "R x y"
    hence "rel_pmf P (f x) (g y)" by(rule that)
    thus False by(auto simp add: P_def f_def g_def rel_pmf_return_pmf2)
  qed
  define R where "R x y = False" for x y :: bool
  have "\<not> rel_pmf R x y" by(simp add: R_def[abs_def])
end

lemma pred_rel_pmf:
  "\<lbrakk> pred_pmf P p; rel_pmf R p q \<rbrakk> \<Longrightarrow> pred_pmf (Imagep R P) q"
unfolding pred_pmf_def
apply(rule ballI)
apply(unfold rel_pmf.simps)
apply(erule exE conjE)+
apply hypsubst
apply(unfold pmf.set_map)
apply(erule imageE, hypsubst)
apply(drule bspec)
 apply(erule rev_image_eqI)
 apply(rule refl)
apply(erule Imagep.intros)
apply(erule allE)+
 apply(erule mp)
apply(unfold prod.collapse)
apply assumption
done

lemma pmf_rel_mono': "\<lbrakk> rel_pmf P x y; P \<le> Q \<rbrakk> \<Longrightarrow> rel_pmf Q x y"
by(drule pmf.rel_mono) (auto)

lemma rel_pmf_eqI [simp]: "rel_pmf (=) x x"
by(simp add: pmf.rel_eq)

lemma rel_pmf_bind_reflI:
  "(\<And>x. x \<in> set_pmf p \<Longrightarrow> rel_pmf R (f x) (g x))
  \<Longrightarrow> rel_pmf R (bind_pmf p f) (bind_pmf p g)"
by(rule rel_pmf_bindI[where R="\<lambda>x y. x = y \<and> x \<in> set_pmf p"])(auto intro: rel_pmf_reflI)

lemma pmf_pred_mono_strong:
  "\<lbrakk> pred_pmf P p; \<And>a. \<lbrakk> a \<in> set_pmf p; P a \<rbrakk> \<Longrightarrow> P' a \<rbrakk> \<Longrightarrow> pred_pmf P' p"
by(simp add: pred_pmf_def)

lemma rel_pmf_restrict_relpI [intro?]:
  "\<lbrakk> rel_pmf R x y; pred_pmf P x; pred_pmf Q y \<rbrakk> \<Longrightarrow> rel_pmf (R \<upharpoonleft> P \<otimes> Q) x y"
by(erule pmf.rel_mono_strong)(simp add: pred_pmf_def)

lemma rel_pmf_restrict_relpE [elim?]:
  assumes "rel_pmf (R \<upharpoonleft> P \<otimes> Q) x y"
  obtains "rel_pmf R x y" "pred_pmf P x" "pred_pmf Q y"
proof
  show "rel_pmf R x y" using assms by(auto elim!: pmf.rel_mono_strong)
  have "pred_pmf (Domainp (R \<upharpoonleft> P \<otimes> Q)) x" using assms by(fold pmf.Domainp_rel) blast
  then show "pred_pmf P x" by(rule pmf_pred_mono_strong)(blast dest!: restrict_relp_DomainpD)
  have "pred_pmf (Domainp (R \<upharpoonleft> P \<otimes> Q)\<inverse>\<inverse>) y" using assms
    by(fold pmf.Domainp_rel)(auto simp only: pmf.rel_conversep Domainp_conversep)
  then show "pred_pmf Q y" by(rule pmf_pred_mono_strong)(auto dest!: restrict_relp_DomainpD)
qed

lemma rel_pmf_restrict_relp_iff:
  "rel_pmf (R \<upharpoonleft> P \<otimes> Q) x y \<longleftrightarrow> rel_pmf R x y \<and> pred_pmf P x \<and> pred_pmf Q y"
by(blast intro: rel_pmf_restrict_relpI elim: rel_pmf_restrict_relpE)

lemma rel_pmf_OO_trans [trans]:
  "\<lbrakk> rel_pmf R p q; rel_pmf S q r \<rbrakk> \<Longrightarrow> rel_pmf (R OO S) p r"
unfolding pmf.rel_compp by blast

lemma pmf_pred_map [simp]: "pred_pmf P (map_pmf f p) = pred_pmf (P \<circ> f) p"
by(simp add: pred_pmf_def)

lemma pred_pmf_bind [simp]: "pred_pmf P (bind_pmf p f) = pred_pmf (pred_pmf P \<circ> f) p"
by(simp add: pred_pmf_def)

lemma pred_pmf_return [simp]: "pred_pmf P (return_pmf x) = P x"
by(simp add: pred_pmf_def)

lemma pred_pmf_of_set [simp]: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> pred_pmf P (pmf_of_set A) = Ball A P"
by(simp add: pred_pmf_def)

lemma pred_pmf_of_multiset [simp]: "M \<noteq> {#} \<Longrightarrow> pred_pmf P (pmf_of_multiset M) = Ball (set_mset M) P"
by(simp add: pred_pmf_def)

lemma pred_pmf_cond [simp]:
  "set_pmf p \<inter> A \<noteq> {} \<Longrightarrow> pred_pmf P (cond_pmf p A) = pred_pmf (\<lambda>x. x \<in> A \<longrightarrow> P x) p"
by(auto simp add: pred_pmf_def)

lemma pred_pmf_pair [simp]:
  "pred_pmf P (pair_pmf p q) = pred_pmf (\<lambda>x. pred_pmf (P \<circ> Pair x) q) p"
by(simp add: pred_pmf_def)

lemma pred_pmf_join [simp]: "pred_pmf P (join_pmf p) = pred_pmf (pred_pmf P) p"
by(simp add: pred_pmf_def)

lemma pred_pmf_bernoulli [simp]: "\<lbrakk> 0 < p; p < 1 \<rbrakk> \<Longrightarrow> pred_pmf P (bernoulli_pmf p) = All P"
by(simp add: pred_pmf_def)

lemma pred_pmf_geometric [simp]: "\<lbrakk> 0 < p; p < 1 \<rbrakk> \<Longrightarrow> pred_pmf P (geometric_pmf p) = All P"
by(simp add: pred_pmf_def set_pmf_geometric)

lemma pred_pmf_poisson [simp]: "0 < rate \<Longrightarrow> pred_pmf P (poisson_pmf rate) = All P"
by(simp add: pred_pmf_def)

lemma pmf_rel_map_restrict_relp: 
  shows pmf_rel_map_restrict_relp1: "rel_pmf (R \<upharpoonleft> P \<otimes> Q) (map_pmf f p) = rel_pmf (R \<circ> f \<upharpoonleft> P \<circ> f \<otimes> Q) p"
  and pmf_rel_map_restrict_relp2: "rel_pmf (R \<upharpoonleft> P \<otimes> Q) p (map_pmf g q) = rel_pmf ((\<lambda>x. R x \<circ> g) \<upharpoonleft> P \<otimes> Q \<circ> g) p q"
by(simp_all add: pmf.rel_map restrict_relp_def fun_eq_iff)

lemma pred_pmf_conj [simp]: "pred_pmf (\<lambda>x. P x \<and> Q x) = (\<lambda>x. pred_pmf P x \<and> pred_pmf Q x)"
by(auto simp add: pred_pmf_def)

lemma pred_pmf_top [simp]:
  "pred_pmf (\<lambda>_. True) = (\<lambda>_. True)"
by(simp add: pred_pmf_def)

lemma rel_pmf_of_setI:
  assumes A: "A \<noteq> {}" "finite A"
  and B: "B \<noteq> {}" "finite B"
  and card: "\<And>X. X \<subseteq> A \<Longrightarrow> card B * card X \<le> card A * card {y\<in>B. \<exists>x\<in>X. R x y}"
  shows "rel_pmf R (pmf_of_set A) (pmf_of_set B)"
apply(rule rel_pmf_measureI)
using assms
apply(clarsimp simp add: measure_pmf_of_set card_gt_0_iff field_simps of_nat_mult[symmetric] simp del: of_nat_mult)
apply(subst mult.commute)
apply(erule meta_allE)
apply(erule meta_impE)
 prefer 2
 apply(erule order_trans)
apply(auto simp add: card_gt_0_iff intro: card_mono)
done

subsection \<open>Subprobability mass functions\<close>

lemma ord_spmf_return_spmf1: "ord_spmf R (return_spmf x) p \<longleftrightarrow> lossless_spmf p \<and> (\<forall>y\<in>set_spmf p. R x y)"
by(auto simp add: rel_pmf_return_pmf1 ord_option.simps in_set_spmf lossless_iff_set_pmf_None Ball_def) (metis option.exhaust)

lemma ord_spmf_conv:
  "ord_spmf R = rel_spmf R OO ord_spmf (=)"
apply(subst pmf.rel_compp[symmetric])
apply(rule arg_cong[where f="rel_pmf"])  
apply(rule ext)+
apply(auto elim!: ord_option.cases option.rel_cases intro: option.rel_intros)
done

lemma ord_spmf_expand:
  "NO_MATCH (=) R \<Longrightarrow> ord_spmf R = rel_spmf R OO ord_spmf (=)"
by(rule ord_spmf_conv)

lemma ord_spmf_eqD_measure: "ord_spmf (=) p q \<Longrightarrow> measure (measure_spmf p) A \<le> measure (measure_spmf q) A"
by(drule ord_spmf_eqD_measure_spmf)(simp add: le_measure measure_spmf.emeasure_eq_measure)

lemma ord_spmf_measureD:
  assumes "ord_spmf R p q"
  shows "measure (measure_spmf p) A \<le> measure (measure_spmf q) {y. \<exists>x\<in>A. R x y}"
    (is "?lhs \<le> ?rhs")
proof -
  from assms obtain p' where *: "rel_spmf R p p'" and **: "ord_spmf (=) p' q"
    by(auto simp add: ord_spmf_expand)
  have "?lhs \<le> measure (measure_spmf p') {y. \<exists>x\<in>A. R x y}" using * by(rule rel_spmf_measureD)
  also have "\<dots> \<le> ?rhs" using ** by(rule ord_spmf_eqD_measure)
  finally show ?thesis .
qed

lemma ord_spmf_bind_pmfI1:
  "(\<And>x. x \<in> set_pmf p \<Longrightarrow> ord_spmf R (f x) q) \<Longrightarrow> ord_spmf R (bind_pmf p f) q"
  apply(rewrite at "ord_spmf _ _ \<hole>" bind_return_pmf[symmetric, where f="\<lambda>_ :: unit. q"])
  apply(rule rel_pmf_bindI[where R="\<lambda>x y. x \<in> set_pmf p"])
  apply(simp_all add: rel_pmf_return_pmf2)
  done
  
lemma ord_spmf_bind_spmfI1:
  "(\<And>x. x \<in> set_spmf p \<Longrightarrow> ord_spmf R (f x) q) \<Longrightarrow> ord_spmf R (bind_spmf p f) q"
unfolding bind_spmf_def by(rule ord_spmf_bind_pmfI1)(auto split: option.split simp add: in_set_spmf)

lemma spmf_of_set_empty: "spmf_of_set {} = return_pmf None"
by(simp add: spmf_of_set_def)

lemma rel_spmf_of_setI:
  assumes card: "\<And>X. X \<subseteq> A \<Longrightarrow> card B * card X \<le> card A * card {y\<in>B. \<exists>x\<in>X. R x y}"
  and eq: "(finite A \<and> A \<noteq> {}) \<longleftrightarrow> (finite B \<and> B \<noteq> {})"
  shows "rel_spmf R (spmf_of_set A) (spmf_of_set B)"
using eq by(clarsimp simp add: spmf_of_set_def card rel_pmf_of_setI simp del: spmf_of_pmf_pmf_of_set cong: conj_cong)

lemmas map_bind_spmf = map_spmf_bind_spmf

lemma nn_integral_measure_spmf_conv_measure_pmf:
  assumes [measurable]: "f \<in> borel_measurable (count_space UNIV)"
  shows "nn_integral (measure_spmf p) f = nn_integral (restrict_space (measure_pmf p) (range Some)) (f \<circ> the)"
by(simp add: measure_spmf_def nn_integral_distr o_def)

lemma nn_integral_spmf_neq_infinity: "(\<integral>\<^sup>+ x. spmf p x \<partial>count_space UNIV) \<noteq> \<infinity>"
using nn_integral_measure_spmf[where f="\<lambda>_. 1", of p, symmetric] by simp

lemma return_pmf_bind_option:
  "return_pmf (Option.bind x f) = bind_spmf (return_pmf x) (return_pmf \<circ> f)"
by(cases x) simp_all

lemma rel_spmf_pos_distr: "rel_spmf A OO rel_spmf B \<le> rel_spmf (A OO B)"
unfolding option.rel_compp pmf.rel_compp ..

lemma rel_spmf_OO_trans [trans]:
  "\<lbrakk> rel_spmf R p q; rel_spmf S q r \<rbrakk> \<Longrightarrow> rel_spmf (R OO S) p r"
by(rule rel_spmf_pos_distr[THEN predicate2D]) auto

lemma map_spmf_eq_map_spmf_iff: "map_spmf f p = map_spmf g q \<longleftrightarrow> rel_spmf (\<lambda>x y. f x = g y) p q"
by(simp add: spmf_rel_eq[symmetric] spmf_rel_map)

lemma map_spmf_eq_map_spmfI: "rel_spmf (\<lambda>x y. f x = g y) p q \<Longrightarrow> map_spmf f p = map_spmf g q"
by(simp add: map_spmf_eq_map_spmf_iff)

lemma spmf_rel_mono_strong:
  "\<lbrakk>rel_spmf A f g; \<And>x y. \<lbrakk> x \<in> set_spmf f; y \<in> set_spmf g; A x y \<rbrakk> \<Longrightarrow> B x y \<rbrakk> \<Longrightarrow> rel_spmf B f g"
apply(erule pmf.rel_mono_strong)
apply(erule option.rel_mono_strong)
by(clarsimp simp add: in_set_spmf)

lemma set_spmf_eq_empty: "set_spmf p = {} \<longleftrightarrow> p = return_pmf None"
by auto (metis restrict_spmf_empty restrict_spmf_trivial)


lemma measure_pair_spmf_times:
  "measure (measure_spmf (pair_spmf p q)) (A \<times> B) = measure (measure_spmf p) A * measure (measure_spmf q) B"
proof -
  have "emeasure (measure_spmf (pair_spmf p q)) (A \<times> B) = (\<integral>\<^sup>+ x. ennreal (spmf (pair_spmf p q) x) * indicator (A \<times> B) x \<partial>count_space UNIV)"
    by(simp add: nn_integral_spmf[symmetric] nn_integral_count_space_indicator)
  also have "\<dots> = (\<integral>\<^sup>+ x. (\<integral>\<^sup>+ y. (ennreal (spmf p x) * indicator A x) * (ennreal (spmf q y) * indicator B y) \<partial>count_space UNIV) \<partial>count_space UNIV)"
    by(subst nn_integral_fst_count_space[symmetric])(auto intro!: nn_integral_cong split: split_indicator simp add: ennreal_mult)
  also have "\<dots> = (\<integral>\<^sup>+ x. ennreal (spmf p x) * indicator A x * emeasure (measure_spmf q) B \<partial>count_space UNIV)"
    by(simp add: nn_integral_cmult nn_integral_spmf[symmetric] nn_integral_count_space_indicator)
  also have "\<dots> = emeasure (measure_spmf p) A * emeasure (measure_spmf q) B"
    by(simp add: nn_integral_multc)(simp add: nn_integral_spmf[symmetric] nn_integral_count_space_indicator)
  finally show ?thesis by(simp add: measure_spmf.emeasure_eq_measure ennreal_mult[symmetric])
qed

lemma lossless_spmfD_set_spmf_nonempty: "lossless_spmf p \<Longrightarrow> set_spmf p \<noteq> {}"
using set_pmf_not_empty[of p] by(auto simp add: set_spmf_def bind_UNION lossless_iff_set_pmf_None)

lemma set_spmf_return_pmf: "set_spmf (return_pmf x) = set_option x"
by(cases x) simp_all

lemma bind_spmf_pmf_assoc: "bind_spmf (bind_pmf p f) g = bind_pmf p (\<lambda>x. bind_spmf (f x) g)"
by(simp add: bind_spmf_def bind_assoc_pmf)

lemma bind_spmf_of_set:  "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> bind_spmf (spmf_of_set A) f = bind_pmf (pmf_of_set A) f"
by(simp add: spmf_of_set_def del: spmf_of_pmf_pmf_of_set)

lemma bind_spmf_map_pmf:
  "bind_spmf (map_pmf f p) g = bind_pmf p (\<lambda>x. bind_spmf (return_pmf (f x)) g)"
by(simp add: map_pmf_def bind_spmf_def bind_assoc_pmf)

lemma rel_spmf_eqI [simp]: "rel_spmf (=) x x"
by(simp add: option.rel_eq)

lemma set_spmf_map_pmf: "set_spmf (map_pmf f p) = (\<Union>x\<in>set_pmf p. set_option (f x))" (* Move up *)
by(simp add: set_spmf_def bind_UNION)

lemma ord_spmf_return_spmf [simp]: "ord_spmf (=) (return_spmf x) p \<longleftrightarrow> p = return_spmf x"
proof -
  have "p = return_spmf x \<Longrightarrow> ord_spmf (=) (return_spmf x) p" by simp
  thus ?thesis
    by (metis (no_types) ord_option_eq_simps(2) rel_pmf_return_pmf1 rel_pmf_return_pmf2 spmf.leq_antisym)
qed

declare
  set_bind_spmf [simp]
  set_spmf_return_pmf [simp]

lemma bind_spmf_pmf_commute:
  "bind_spmf p (\<lambda>x. bind_pmf q (f x)) = bind_pmf q (\<lambda>y. bind_spmf p (\<lambda>x. f x y))"
unfolding bind_spmf_def 
by(subst bind_commute_pmf)(auto intro: bind_pmf_cong[OF refl] split: option.split)

lemma return_pmf_map_option_conv_bind:
  "return_pmf (map_option f x) = bind_spmf (return_pmf x) (return_spmf \<circ> f)"
by(cases x) simp_all

lemma lossless_return_pmf_iff [simp]: "lossless_spmf (return_pmf x) \<longleftrightarrow> x \<noteq> None"
by(cases x) simp_all

lemma lossless_map_pmf: "lossless_spmf (map_pmf f p) \<longleftrightarrow> (\<forall>x \<in> set_pmf p. f x \<noteq> None)"
using image_iff by(fastforce simp add: lossless_iff_set_pmf_None)

lemma bind_pmf_spmf_assoc:
  "g None = return_pmf None
  \<Longrightarrow> bind_pmf (bind_spmf p f) g = bind_spmf p (\<lambda>x. bind_pmf (f x) g)"
by(auto simp add: bind_spmf_def bind_assoc_pmf bind_return_pmf fun_eq_iff intro!: arg_cong2[where f=bind_pmf] split: option.split)

abbreviation pred_spmf :: "('a \<Rightarrow> bool) \<Rightarrow> 'a spmf \<Rightarrow> bool"
where "pred_spmf P \<equiv> pred_pmf (pred_option P)"

lemma pred_spmf_def: "pred_spmf P p \<longleftrightarrow> (\<forall>x\<in>set_spmf p. P x)"
by(auto simp add: pred_pmf_def pred_option_def set_spmf_def)

lemma spmf_pred_mono_strong:
  "\<lbrakk> pred_spmf P p; \<And>a. \<lbrakk> a \<in> set_spmf p; P a \<rbrakk> \<Longrightarrow> P' a \<rbrakk> \<Longrightarrow> pred_spmf P' p"
by(simp add: pred_spmf_def)

lemma spmf_Domainp_rel: "Domainp (rel_spmf R) = pred_spmf (Domainp R)"
by(simp add: pmf.Domainp_rel option.Domainp_rel)

lemma rel_spmf_restrict_relpI [intro?]:
  "\<lbrakk> rel_spmf R p q; pred_spmf P p; pred_spmf Q q \<rbrakk> \<Longrightarrow> rel_spmf (R \<upharpoonleft> P \<otimes> Q) p q"
by(erule spmf_rel_mono_strong)(simp add: pred_spmf_def)

lemma rel_spmf_restrict_relpE [elim?]:
  assumes "rel_spmf (R \<upharpoonleft> P \<otimes> Q) x y"
  obtains "rel_spmf R x y" "pred_spmf P x" "pred_spmf Q y"
proof
  show "rel_spmf R x y" using assms by(auto elim!: spmf_rel_mono_strong)
  have "pred_spmf (Domainp (R \<upharpoonleft> P \<otimes> Q)) x" using assms by(fold spmf_Domainp_rel) blast
  then show "pred_spmf P x" by(rule spmf_pred_mono_strong)(blast dest!: restrict_relp_DomainpD)
  have "pred_spmf (Domainp (R \<upharpoonleft> P \<otimes> Q)\<inverse>\<inverse>) y" using assms
    by(fold spmf_Domainp_rel)(auto simp only: spmf_rel_conversep Domainp_conversep)
  then show "pred_spmf Q y" by(rule spmf_pred_mono_strong)(auto dest!: restrict_relp_DomainpD)
qed

lemma rel_spmf_restrict_relp_iff:
  "rel_spmf (R \<upharpoonleft> P \<otimes> Q) x y \<longleftrightarrow> rel_spmf R x y \<and> pred_spmf P x \<and> pred_spmf Q y"
by(blast intro: rel_spmf_restrict_relpI elim: rel_spmf_restrict_relpE)

lemma spmf_pred_map: "pred_spmf P (map_spmf f p) = pred_spmf (P \<circ> f) p"
by(simp)

lemma pred_spmf_bind [simp]: "pred_spmf P (bind_spmf p f) = pred_spmf (pred_spmf P \<circ> f) p"
by(simp add: pred_spmf_def bind_UNION)

lemma pred_spmf_return: "pred_spmf P (return_spmf x) = P x"
by simp

lemma pred_spmf_return_pmf_None: "pred_spmf P (return_pmf None)"
by simp

lemma pred_spmf_spmf_of_pmf [simp]: "pred_spmf P (spmf_of_pmf p) = pred_pmf P p"
unfolding pred_spmf_def by(simp add: pred_pmf_def)

lemma pred_spmf_of_set [simp]: "pred_spmf P (spmf_of_set A) = (finite A \<longrightarrow> Ball A P)"
by(auto simp add: pred_spmf_def set_spmf_of_set)

lemma pred_spmf_assert_spmf [simp]: "pred_spmf P (assert_spmf b) = (b \<longrightarrow> P ())"
by(cases b) simp_all

lemma pred_spmf_pair [simp]:
  "pred_spmf P (pair_spmf p q) = pred_spmf (\<lambda>x. pred_spmf (P \<circ> Pair x) q) p"
by(simp add: pred_spmf_def)

lemma set_spmf_try [simp]:
  "set_spmf (try_spmf p q) = set_spmf p \<union> (if lossless_spmf p then {} else set_spmf q)"
by(auto simp add: try_spmf_def set_spmf_bind_pmf in_set_spmf lossless_iff_set_pmf_None split: option.splits)(metis option.collapse)

lemma try_spmf_bind_out1:
  "(\<And>x. lossless_spmf (f x)) \<Longrightarrow> bind_spmf (TRY p ELSE q) f = TRY (bind_spmf p f) ELSE (bind_spmf q f)"
  apply(clarsimp simp add: bind_spmf_def try_spmf_def bind_assoc_pmf bind_return_pmf intro!: bind_pmf_cong[OF refl] split: option.split)
  apply(rewrite in "\<hole> = _" bind_return_pmf'[symmetric])
  apply(rule bind_pmf_cong[OF refl])
  apply(clarsimp split: option.split simp add: lossless_iff_set_pmf_None)
  done

lemma pred_spmf_try [simp]:
  "pred_spmf P (try_spmf p q) = (pred_spmf P p \<and> (\<not> lossless_spmf p \<longrightarrow> pred_spmf P q))"
by(auto simp add: pred_spmf_def)

lemma pred_spmf_cond [simp]:
  "pred_spmf P (cond_spmf p A) = pred_spmf (\<lambda>x. x \<in> A \<longrightarrow> P x) p"
by(auto simp add: pred_spmf_def)

lemma spmf_rel_map_restrict_relp: 
  shows spmf_rel_map_restrict_relp1: "rel_spmf (R \<upharpoonleft> P \<otimes> Q) (map_spmf f p) = rel_spmf (R \<circ> f \<upharpoonleft> P \<circ> f \<otimes> Q) p"
  and spmf_rel_map_restrict_relp2: "rel_spmf (R \<upharpoonleft> P \<otimes> Q) p (map_spmf g q) = rel_spmf ((\<lambda>x. R x \<circ> g) \<upharpoonleft> P \<otimes> Q \<circ> g) p q"
by(simp_all add: spmf_rel_map restrict_relp_def)

lemma pred_spmf_conj: "pred_spmf (\<lambda>x. P x \<and> Q x) = (\<lambda>x. pred_spmf P x \<and> pred_spmf Q x)"
by simp


lemma spmf_of_pmf_parametric [transfer_rule]: 
  includes lifting_syntax shows
  "(rel_pmf A ===> rel_spmf A) spmf_of_pmf spmf_of_pmf"
unfolding spmf_of_pmf_def[abs_def] by transfer_prover

lemma mono2mono_return_pmf[THEN spmf.mono2mono, simp, cont_intro]: (* Move to SPMF *)
  shows monotone_return_pmf: "monotone option_ord (ord_spmf (=)) return_pmf"
by(rule monotoneI)(auto simp add: flat_ord_def)

lemma mcont2mcont_return_pmf[THEN spmf.mcont2mcont, simp, cont_intro]:  (* Move to SPMF *)
  shows mcont_return_pmf: "mcont (flat_lub None) option_ord lub_spmf (ord_spmf (=)) return_pmf"
by(rule mcont_finite_chains[OF _ _ flat_interpretation[THEN ccpo] ccpo_spmf]) simp_all

lemma pred_spmf_top: (* Move up *)
  "pred_spmf (\<lambda>_. True) = (\<lambda>_. True)"
by(simp)

lemma rel_spmf_restrict_relpI' [intro?]:
  "\<lbrakk> rel_spmf (\<lambda>x y. P x \<longrightarrow> Q y \<longrightarrow> R x y) p q; pred_spmf P p; pred_spmf Q q \<rbrakk> \<Longrightarrow> rel_spmf (R \<upharpoonleft> P \<otimes> Q) p q"
by(erule spmf_rel_mono_strong)(simp add: pred_spmf_def)

lemma set_spmf_map_pmf_MATCH [simp]:
  assumes "NO_MATCH (map_option g) f"
  shows "set_spmf (map_pmf f p) = (\<Union>x\<in>set_pmf p. set_option (f x))"
by(rule set_spmf_map_pmf)

lemma rel_spmf_bindI':
  "\<lbrakk> rel_spmf A p q; \<And>x y. \<lbrakk> A x y; x \<in> set_spmf p; y \<in> set_spmf q \<rbrakk> \<Longrightarrow> rel_spmf B (f x) (g y) \<rbrakk>
  \<Longrightarrow> rel_spmf B (p \<bind> f) (q \<bind> g)"
apply(rule rel_spmf_bindI[where R="\<lambda>x y. A x y \<and> x \<in> set_spmf p \<and> y \<in> set_spmf q"])
 apply(erule spmf_rel_mono_strong; simp)
apply simp
done


subsubsection \<open>Embedding of @{typ "'a option"} into @{typ "'a spmf"}\<close>

text \<open>This theoretically follows from the embedding between @{typ "_ id"} into @{typ "_ prob"} and the isomorphism
  between @{typ "(_, _ prob) optionT"} and @{typ "_ spmf"}, but we would only get the monomorphic
  version via this connection. So we do it directly.
\<close>

lemma bind_option_spmf_monad [simp]: "monad.bind_option (return_pmf None) x = bind_spmf (return_pmf x)"
by(cases x)(simp_all add: fun_eq_iff)

locale option_to_spmf begin

text \<open>
  We have to get the embedding into the lifting package such that we can use the parametrisation of transfer rules.
\<close>

definition the_pmf :: "'a pmf \<Rightarrow> 'a" where "the_pmf p = (THE x. p = return_pmf x)"

lemma the_pmf_return [simp]: "the_pmf (return_pmf x) = x"
by(simp add: the_pmf_def)

lemma type_definition_option_spmf: "type_definition return_pmf the_pmf {x. \<exists>y :: 'a option. x = return_pmf y}"
by unfold_locales(auto)

context begin
private setup_lifting type_definition_option_spmf
abbreviation cr_spmf_option where "cr_spmf_option \<equiv> cr_option"
abbreviation pcr_spmf_option where "pcr_spmf_option \<equiv> pcr_option"
lemmas Quotient_spmf_option = Quotient_option
  and cr_spmf_option_def = cr_option_def
  and pcr_spmf_option_bi_unique = option.bi_unique
  and Domainp_pcr_spmf_option = option.domain
  and Domainp_pcr_spmf_option_eq = option.domain_eq
  and Domainp_pcr_spmf_option_par = option.domain_par
  and Domainp_pcr_spmf_option_left_total = option.domain_par_left_total
  and pcr_spmf_option_left_unique = option.left_unique
  and pcr_spmf_option_cr_eq = option.pcr_cr_eq
  and pcr_spmf_option_return_pmf_transfer = option.rep_transfer
  and pcr_spmf_option_right_total = option.right_total
  and pcr_spmf_option_right_unique = option.right_unique
  and pcr_spmf_option_def = pcr_option_def
bundle spmf_option_lifting = [[Lifting.lifting_restore_internal "Misc_CryptHOL.option.lifting"]]
end


context includes lifting_syntax begin

lemma return_option_spmf_transfer [transfer_parametric return_spmf_parametric, transfer_rule]:
  "((=) ===> cr_spmf_option) return_spmf Some"
by(rule rel_funI)(simp add: cr_spmf_option_def)

lemma map_option_spmf_transfer [transfer_parametric map_spmf_parametric, transfer_rule]:
  "(((=) ===> (=)) ===> cr_spmf_option ===> cr_spmf_option) map_spmf map_option"
unfolding rel_fun_eq by(auto simp add: rel_fun_def cr_spmf_option_def)

lemma fail_option_spmf_transfer [transfer_parametric return_spmf_None_parametric, transfer_rule]:
  "cr_spmf_option (return_pmf None) None"
by(simp add: cr_spmf_option_def)

lemma bind_option_spmf_transfer [transfer_parametric bind_spmf_parametric, transfer_rule]:
  "(cr_spmf_option ===> ((=) ===> cr_spmf_option) ===> cr_spmf_option) bind_spmf Option.bind"
apply(clarsimp simp add: rel_fun_def cr_spmf_option_def)
subgoal for x f g by(cases x; simp)
done

lemma set_option_spmf_transfer [transfer_parametric set_spmf_parametric, transfer_rule]:
  "(cr_spmf_option ===> rel_set (=)) set_spmf set_option"
by(clarsimp simp add: rel_fun_def cr_spmf_option_def rel_set_eq)

lemma rel_option_spmf_transfer [transfer_parametric rel_spmf_parametric, transfer_rule]:
  "(((=) ===> (=) ===> (=)) ===> cr_spmf_option ===> cr_spmf_option ===> (=)) rel_spmf rel_option"
unfolding rel_fun_eq by(simp add: rel_fun_def cr_spmf_option_def)

end

end

locale option_le_spmf begin

text \<open>
  Embedding where only successful computations in the option monad are related to Dirac spmf.
\<close>

definition cr_option_le_spmf :: "'a option \<Rightarrow> 'a spmf \<Rightarrow> bool"
where "cr_option_le_spmf x p \<longleftrightarrow> ord_spmf (=) (return_pmf x) p"

context includes lifting_syntax begin

lemma return_option_le_spmf_transfer [transfer_rule]:
  "((=) ===> cr_option_le_spmf) (\<lambda>x. x) return_pmf"
by(rule rel_funI)(simp add: cr_option_le_spmf_def ord_option_reflI)

lemma map_option_le_spmf_transfer [transfer_rule]:
  "(((=) ===> (=)) ===> cr_option_le_spmf ===> cr_option_le_spmf) map_option map_spmf"
unfolding rel_fun_eq
apply(clarsimp simp add: rel_fun_def cr_option_le_spmf_def rel_pmf_return_pmf1 ord_option_map1 ord_option_map2)
subgoal for f x p y by(cases x; simp add: ord_option_reflI)
done

lemma bind_option_le_spmf_transfer [transfer_rule]:
  "(cr_option_le_spmf ===> ((=) ===> cr_option_le_spmf) ===> cr_option_le_spmf) Option.bind bind_spmf"
apply(clarsimp simp add: rel_fun_def cr_option_le_spmf_def)
subgoal for x p f g by(cases x; auto 4 3 simp add: rel_pmf_return_pmf1 set_pmf_bind_spmf)
done

end

end

interpretation rel_spmf_characterisation by unfold_locales(rule rel_pmf_measureI)

lemma if_distrib_bind_spmf1 [if_distribs]:
  "bind_spmf (if b then x else y) f = (if b then bind_spmf x f else bind_spmf y f)"
by simp

lemma if_distrib_bind_spmf2 [if_distribs]:
  "bind_spmf x (\<lambda>y. if b then f y else g y) = (if b then bind_spmf x f else bind_spmf x g)"
by simp

lemma rel_spmf_if_distrib [if_distribs]:
  "rel_spmf R (if b then x else y) (if b then x' else y') \<longleftrightarrow>
  (b \<longrightarrow> rel_spmf R x x') \<and> (\<not> b \<longrightarrow> rel_spmf R y y')"
by(simp)

lemma if_distrib_map_spmf [if_distribs]:
  "map_spmf f (if b then p else q) = (if b then map_spmf f p else map_spmf f q)"
by simp

lemma if_distrib_restrict_spmf1 [if_distribs]:
  "restrict_spmf (if b then p else q) A = (if b then restrict_spmf p A else restrict_spmf q A)"
by simp

end
