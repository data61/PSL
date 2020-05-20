(* Title: Partial_Function_Set.thy
  Author: Andreas Lochbihler, ETH Zurich *)

theory Partial_Function_Set imports Main begin

subsection \<open>Setup for \<open>partial_function\<close> for sets\<close>

lemma (in complete_lattice) lattice_partial_function_definition:
  "partial_function_definitions (\<le>) Sup"
by(unfold_locales)(auto intro: Sup_upper Sup_least)

interpretation set: partial_function_definitions "(\<subseteq>)" Union
by(rule lattice_partial_function_definition)

lemma fun_lub_Sup: "fun_lub Sup = (Sup :: _ \<Rightarrow> _ :: complete_lattice)"
by(fastforce simp add: fun_lub_def fun_eq_iff Sup_fun_def intro: Sup_eqI SUP_upper SUP_least)

lemma set_admissible: "set.admissible (\<lambda>f :: 'a \<Rightarrow> 'b set. \<forall>x y. y \<in> f x \<longrightarrow> P x y)"
by(rule ccpo.admissibleI)(auto simp add: fun_lub_Sup)

abbreviation "mono_set \<equiv> monotone (fun_ord (\<subseteq>)) (\<subseteq>)"

lemma fixp_induct_set_scott:
  fixes F :: "'c \<Rightarrow> 'c"
  and U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a set"
  and C :: "('b \<Rightarrow> 'a set) \<Rightarrow> 'c"
  and P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  and x and y
  assumes mono: "\<And>x. mono_set (\<lambda>f. U (F (C f)) x)"
  and eq: "f \<equiv> C (ccpo.fixp (fun_lub Sup) (fun_ord (\<le>)) (\<lambda>f. U (F (C f))))"
  and inverse2: "\<And>f. U (C f) = f"
  and step: "\<And>f x y. \<lbrakk> \<And>x y. y \<in> U f x \<Longrightarrow> P x y; y \<in> U (F f) x \<rbrakk> \<Longrightarrow> P x y"
  and enforce_variable_ordering: "x = x"
  and elem: "y \<in> U f x"
  shows "P x y"
using step elem set.fixp_induct_uc[of U F C, OF mono eq inverse2 set_admissible, of P]
by blast


lemma fixp_Sup_le:
  defines "le \<equiv> ((\<le>) :: _ :: complete_lattice \<Rightarrow> _)"
  shows "ccpo.fixp Sup le = ccpo_class.fixp"
proof -
  have "class.ccpo Sup le (<)" unfolding le_def by unfold_locales
  thus ?thesis
    by(simp add: ccpo.fixp_def fixp_def ccpo.iterates_def iterates_def ccpo.iteratesp_def iteratesp_def fun_eq_iff le_def)
qed

lemma fun_ord_le: "fun_ord (\<le>) = (\<le>)"
by(auto simp add: fun_ord_def fun_eq_iff le_fun_def)

lemma monotone_le_le: "monotone (\<le>) (\<le>) = mono"
by(simp add: monotone_def[abs_def] mono_def[abs_def])

lemma fixp_induct_set:
  fixes F :: "'c \<Rightarrow> 'c"
  and U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a set"
  and C :: "('b \<Rightarrow> 'a set) \<Rightarrow> 'c"
  and P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  and x and y
  assumes mono: "\<And>x. mono_set (\<lambda>f. U (F (C f)) x)"
  and eq: "f \<equiv> C (ccpo.fixp (fun_lub Sup) (fun_ord (\<le>)) (\<lambda>f. U (F (C f))))"
  and inverse2: "\<And>f. U (C f) = f"

  and step: "\<And>f' x y. \<lbrakk> \<And>x. U f' x = U f' x; y \<in> U (F (C (inf (U f) (\<lambda>x. {y. P x y})))) x \<rbrakk> \<Longrightarrow> P x y"
    \<comment> \<open>partial\_function requires a quantifier over f', so let's have a fake one\<close>
  and elem: "y \<in> U f x"
  shows "P x y"
proof -
  from mono
  have mono': "mono (\<lambda>f. U (F (C f)))"
    by(simp add: fun_ord_le monotone_le_le mono_def le_fun_def)
  hence eq': "f \<equiv> C (lfp (\<lambda>f. U (F (C f))))"
    using eq unfolding fun_ord_le fun_lub_Sup fixp_Sup_le by(simp add: lfp_eq_fixp)

  let ?f = "C (lfp (\<lambda>f. U (F (C f))))"
  have step': "\<And>x y. \<lbrakk> y \<in> U (F (C (inf (U ?f) (\<lambda>x. {y. P x y})))) x \<rbrakk> \<Longrightarrow> P x y"
    unfolding eq'[symmetric] by(rule step[OF refl])

  let ?P = "\<lambda>x. {y. P x y}"
  from mono' have "lfp (\<lambda>f. U (F (C f))) \<le> ?P"
    by(rule lfp_induct)(auto intro!: le_funI step' simp add: inverse2)
  with elem show ?thesis
    by(subst (asm) eq')(auto simp add: inverse2 le_fun_def)
qed

declaration \<open>Partial_Function.init "set" @{term set.fixp_fun}
  @{term set.mono_body} @{thm set.fixp_rule_uc} @{thm set.fixp_induct_uc}
  (SOME @{thm fixp_induct_set})\<close>

lemma [partial_function_mono]:
  shows insert_mono: "mono_set A \<Longrightarrow> mono_set (\<lambda>f. insert x (A f))"
  and UNION_mono: "\<lbrakk>mono_set B; \<And>y. mono_set (\<lambda>f. C y f)\<rbrakk> \<Longrightarrow> mono_set (\<lambda>f. \<Union>y\<in>B f. C y f)"
  and set_bind_mono: "\<lbrakk>mono_set B; \<And>y. mono_set (\<lambda>f. C y f)\<rbrakk> \<Longrightarrow> mono_set (\<lambda>f. Set.bind (B f) (\<lambda>y. C y f))"
  and Un_mono: "\<lbrakk> mono_set A; mono_set B \<rbrakk> \<Longrightarrow> mono_set (\<lambda>f. A f \<union> B f)"
  and Int_mono: "\<lbrakk> mono_set A; mono_set B \<rbrakk> \<Longrightarrow> mono_set (\<lambda>f. A f \<inter> B f)"
  and Diff_mono1: "mono_set A \<Longrightarrow> mono_set (\<lambda>f. A f - X)"
  and image_mono: "mono_set A \<Longrightarrow> mono_set (\<lambda>f. g ` A f)"
  and vimage_mono: "mono_set A \<Longrightarrow> mono_set (\<lambda>f. g -` A f)"
unfolding bind_UNION by(fast intro!: monotoneI dest: monotoneD)+

partial_function (set) test :: "'a list \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> int set"
where
  "test xs i j = insert 4 (test [] 0 j \<union> test [] 1 True \<inter> test [] 2 False - {5} \<union> uminus ` test [undefined] 0 True \<union> uminus -` test [] 1 False)"

interpretation coset: partial_function_definitions "(\<supseteq>)" Inter
by(rule complete_lattice.lattice_partial_function_definition[OF dual_complete_lattice])

lemma fun_lub_Inf: "fun_lub Inf = (Inf :: _ \<Rightarrow> _ :: complete_lattice)"
by(auto simp add: fun_lub_def fun_eq_iff Inf_fun_def intro: Inf_eqI INF_lower INF_greatest)

lemma fun_ord_ge: "fun_ord (\<ge>) = (\<ge>)"
by(auto simp add: fun_ord_def fun_eq_iff le_fun_def)

lemma coset_admissible: "coset.admissible (\<lambda>f :: 'a \<Rightarrow> 'b set. \<forall>x y. P x y \<longrightarrow> y \<in> f x)"
by(rule ccpo.admissibleI)(auto simp add: fun_lub_Inf)

abbreviation "mono_coset \<equiv> monotone (fun_ord (\<supseteq>)) (\<supseteq>)"

lemma gfp_eq_fixp:
  fixes f :: "'a :: complete_lattice \<Rightarrow> 'a"
  assumes f: "monotone (\<ge>) (\<ge>) f"
  shows "gfp f = ccpo.fixp Inf (\<ge>) f"
proof (rule antisym)
  from f have f': "mono f" by(simp add: mono_def monotone_def)

  interpret ccpo Inf "(\<ge>)" "mk_less (\<ge>) :: 'a \<Rightarrow> _"
    by(rule ccpo)(rule complete_lattice.lattice_partial_function_definition[OF dual_complete_lattice])
  show "ccpo.fixp Inf (\<ge>) f \<le> gfp f"
    by(rule gfp_upperbound)(subst fixp_unfold[OF f], rule order_refl)

  show "gfp f \<le> ccpo.fixp Inf (\<ge>) f"
    by(rule fixp_lowerbound[OF f])(subst gfp_unfold[OF f'], rule order_refl)
qed

lemma fixp_coinduct_set:
  fixes F :: "'c \<Rightarrow> 'c"
  and U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a set"
  and C :: "('b \<Rightarrow> 'a set) \<Rightarrow> 'c"
  and P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  and x and y
  assumes mono: "\<And>x. mono_coset (\<lambda>f. U (F (C f)) x)"
  and eq: "f \<equiv> C (ccpo.fixp (fun_lub Inter) (fun_ord (\<ge>)) (\<lambda>f. U (F (C f))))"
  and inverse2: "\<And>f. U (C f) = f"

  and step: "\<And>f' x y. \<lbrakk> \<And>x. U f' x = U f' x; \<not> P x y \<rbrakk> \<Longrightarrow> y \<in> U (F (C (sup (\<lambda>x. {y. \<not> P x y}) (U f)))) x"
    \<comment> \<open>partial\_function requires a quantifier over f', so let's have a fake one\<close>
  and elem: "y \<notin> U f x"
  shows "P x y"
using elem
proof(rule contrapos_np)
  have mono': "monotone (\<ge>) (\<ge>) (\<lambda>f. U (F (C f)))"
    and mono'': "mono (\<lambda>f. U (F (C f)))"
    using mono by(simp_all add: monotone_def fun_ord_def le_fun_def mono_def)
  hence eq': "U f = gfp (\<lambda>f. U (F (C f)))"
    by(subst eq)(simp add: fun_lub_Inf fun_ord_ge gfp_eq_fixp inverse2)

  let ?P = "\<lambda>x. {y. \<not> P x y}"
  have "?P \<le> gfp (\<lambda>f. U (F (C f)))"
    using mono'' by(rule coinduct)(auto intro!:  le_funI dest: step[OF refl] simp add: eq')
  moreover
  assume "\<not> P x y"
  ultimately show "y \<in> U f x" by(auto simp add: le_fun_def eq')
qed

declaration \<open>Partial_Function.init "coset" @{term coset.fixp_fun}
  @{term coset.mono_body} @{thm coset.fixp_rule_uc} @{thm coset.fixp_induct_uc}
  (SOME @{thm fixp_coinduct_set})\<close>

abbreviation "mono_set' \<equiv> monotone (fun_ord (\<supseteq>)) (\<supseteq>)"

lemma [partial_function_mono]:
  shows insert_mono': "mono_set' A \<Longrightarrow> mono_set' (\<lambda>f. insert x (A f))"
  and UNION_mono': "\<lbrakk>mono_set' B; \<And>y. mono_set' (\<lambda>f. C y f)\<rbrakk> \<Longrightarrow> mono_set' (\<lambda>f. \<Union>y\<in>B f. C y f)"
  and set_bind_mono': "\<lbrakk>mono_set' B; \<And>y. mono_set' (\<lambda>f. C y f)\<rbrakk> \<Longrightarrow> mono_set' (\<lambda>f. Set.bind (B f) (\<lambda>y. C y f))"
  and Un_mono': "\<lbrakk> mono_set' A; mono_set' B \<rbrakk> \<Longrightarrow> mono_set' (\<lambda>f. A f \<union> B f)"
  and Int_mono': "\<lbrakk> mono_set' A; mono_set' B \<rbrakk> \<Longrightarrow> mono_set' (\<lambda>f. A f \<inter> B f)"
unfolding bind_UNION by(fast intro!: monotoneI dest: monotoneD)+

context begin
private partial_function (coset) test2 :: "nat \<Rightarrow> nat set"
where "test2 x = insert x (test2 (Suc x))"

private lemma test2_coinduct:
  assumes "P x y"
  and *: "\<And>x y. P x y \<Longrightarrow> y = x \<or> (P (Suc x) y \<or> y \<in> test2 (Suc x))"
  shows "y \<in> test2 x"
using \<open>P x y\<close>
apply(rule contrapos_pp)
apply(erule test2.raw_induct[rotated])
apply(simp add: *)
done

end

end
