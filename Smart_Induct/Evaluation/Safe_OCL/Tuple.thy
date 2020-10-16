(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
(* TODO: There are a lot of similar lemmas in the theory.
         They should be generalized *)
section \<open>Tuples\<close>
theory Tuple
  imports Finite_Map_Ext Transitive_Closure_Ext
begin

subsection \<open>Definitions\<close>

abbreviation "subtuple f xm ym \<equiv> fmrel_on_fset (fmdom ym) f xm ym"

abbreviation "strict_subtuple f xm ym \<equiv> subtuple f xm ym \<and> xm \<noteq> ym"

(*** Helper Lemmas **********************************************************)

subsection \<open>Helper Lemmas\<close>

lemma fmrel_to_subtuple:
  "fmrel r xm ym \<Longrightarrow> subtuple r xm ym"
  unfolding fmrel_on_fset_fmrel_restrict by blast

lemma subtuple_eq_fmrel_fmrestrict_fset:
  "subtuple r xm ym = fmrel r (fmrestrict_fset (fmdom ym) xm) ym"
  by (simp add: fmrel_on_fset_fmrel_restrict)

lemma subtuple_fmdom:
  "subtuple f xm ym \<Longrightarrow>
   subtuple g ym xm \<Longrightarrow>
   fmdom xm = fmdom ym"
  by (meson fmrel_on_fset_fmdom fset_eqI)

(*** Basic Properties *******************************************************)

subsection \<open>Basic Properties\<close>

lemma subtuple_refl:
  "reflp R \<Longrightarrow> subtuple R xm xm"
  by (simp add: fmrel_on_fsetI option.rel_reflp reflpD)

lemma subtuple_mono [mono]:
  "(\<And>x y. x \<in> fmran' xm \<Longrightarrow> y \<in> fmran' ym \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow>
   subtuple f xm ym \<longrightarrow> subtuple g xm ym"
  apply (auto)
  apply (rule fmrel_on_fsetI)
  apply (drule_tac ?P="f" and ?m="xm" and ?n="ym" in fmrel_on_fsetD, simp)
  apply (erule option.rel_cases, simp)
  by (auto simp add: option.rel_sel fmran'I)

lemma strict_subtuple_mono [mono]:
  "(\<And>x y. x \<in> fmran' xm \<Longrightarrow> y \<in> fmran' ym \<Longrightarrow> f x y \<longrightarrow> g x y) \<Longrightarrow>
   strict_subtuple f xm ym \<longrightarrow> strict_subtuple g xm ym"
  using subtuple_mono by blast

lemma subtuple_antisym:
  assumes "subtuple (\<lambda>x y. f x y \<or> x = y) xm ym"
  assumes "subtuple (\<lambda>x y. f x y \<and> \<not> f y x \<or> x = y) ym xm"
  shows "xm = ym"
proof (rule fmap_ext)
  fix x
  from assms have "fmdom xm = fmdom ym"
    using subtuple_fmdom by blast
  with assms have "fmrel (\<lambda>x y. f x y \<or> x = y) xm ym"
      and "fmrel (\<lambda>x y. f x y \<and> \<not> f y x \<or> x = y) ym xm"
    by (metis (mono_tags, lifting) fmrel_code fmrel_on_fset_alt_def)+
  thus "fmlookup xm x = fmlookup ym x"
    apply (erule_tac ?x="x" in fmrel_cases)
    by (erule_tac ?x="x" in fmrel_cases, auto)+
qed

lemma strict_subtuple_antisym:
  "strict_subtuple (\<lambda>x y. f x y \<or> x = y) xm ym \<Longrightarrow>
   strict_subtuple (\<lambda>x y. f x y \<and> \<not> f y x \<or> x = y) ym xm \<Longrightarrow> False"
  by (auto simp add: subtuple_antisym)

lemma subtuple_acyclic:
  assumes "acyclicP_on (fmran' xm) P"
  assumes "subtuple (\<lambda>x y. P x y \<or> x = y)\<^sup>+\<^sup>+ xm ym"
  assumes "subtuple (\<lambda>x y. P x y \<or> x = y) ym xm"
  shows "xm = ym"
proof (rule fmap_ext)
  fix x
  from assms have fmdom_eq: "fmdom xm = fmdom ym"
    using subtuple_fmdom by blast
  have "\<And>x a b. acyclicP_on (fmran' xm) P \<Longrightarrow>
     fmlookup xm x = Some a \<Longrightarrow>
     fmlookup ym x = Some b \<Longrightarrow>
    P\<^sup>*\<^sup>* a b \<Longrightarrow> P b a \<or> a = b \<Longrightarrow> a = b"
    by (meson Nitpick.tranclp_unfold fmran'I rtranclp_into_tranclp1)
  moreover from fmdom_eq assms(2) have "fmrel P\<^sup>*\<^sup>* xm ym"
    unfolding fmrel_on_fset_fmrel_restrict apply auto
    by (metis fmrestrict_fset_dom)
  moreover from fmdom_eq assms(3) have "fmrel (\<lambda>x y. P x y \<or> x = y) ym xm"
    unfolding fmrel_on_fset_fmrel_restrict apply auto
    by (metis fmrestrict_fset_dom)
  ultimately show "fmlookup xm x = fmlookup ym x"
    apply (erule_tac ?x="x" in fmrel_cases)
    apply (erule_tac ?x="x" in fmrel_cases, simp_all)+
    using assms(1) by blast
qed

lemma subtuple_acyclic':
  assumes "acyclicP_on (fmran' ym) P"
  assumes "subtuple (\<lambda>x y. P x y \<or> x = y)\<^sup>+\<^sup>+ xm ym"
  assumes "subtuple (\<lambda>x y. P x y \<or> x = y) ym xm"
  shows "xm = ym"
proof (rule fmap_ext)
  fix x
  from assms have fmdom_eq: "fmdom xm = fmdom ym"
    using subtuple_fmdom by blast
  have "\<And>x a b. acyclicP_on (fmran' ym) P \<Longrightarrow>
     fmlookup xm x = Some a \<Longrightarrow>
     fmlookup ym x = Some b \<Longrightarrow>
    P\<^sup>*\<^sup>* a b \<Longrightarrow> P b a \<or> a = b \<Longrightarrow> a = b"
    by (meson Nitpick.tranclp_unfold fmran'I rtranclp_into_tranclp2)
  moreover from fmdom_eq assms(2) have "fmrel P\<^sup>*\<^sup>* xm ym"
    unfolding fmrel_on_fset_fmrel_restrict apply auto
    by (metis fmrestrict_fset_dom)
  moreover from fmdom_eq assms(3) have "fmrel (\<lambda>x y. P x y \<or> x = y) ym xm"
    unfolding fmrel_on_fset_fmrel_restrict apply auto
    by (metis fmrestrict_fset_dom)
  ultimately show "fmlookup xm x = fmlookup ym x"
    apply (erule_tac ?x="x" in fmrel_cases)
    apply (erule_tac ?x="x" in fmrel_cases, simp_all)+
    using assms(1) by blast
qed

lemma subtuple_acyclic'':
  "acyclicP_on (fmran' ym) R \<Longrightarrow>
   subtuple R\<^sup>*\<^sup>* xm ym \<Longrightarrow>
   subtuple R ym xm \<Longrightarrow>
   xm = ym"
  by (metis (no_types, lifting) subtuple_acyclic' subtuple_mono tranclp_eq_rtranclp)

lemma strict_subtuple_trans:
  "acyclicP_on (fmran' xm) P \<Longrightarrow>
   strict_subtuple (\<lambda>x y. P x y \<or> x = y)\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   strict_subtuple (\<lambda>x y. P x y \<or> x = y) ym zm \<Longrightarrow>
   strict_subtuple (\<lambda>x y. P x y \<or> x = y)\<^sup>+\<^sup>+ xm zm"
  apply auto
  apply (rule fmrel_on_fset_trans, auto)
  by (drule_tac ?ym="ym" in subtuple_acyclic; auto)

lemma strict_subtuple_trans':
  "acyclicP_on (fmran' zm) P \<Longrightarrow>
   strict_subtuple (\<lambda>x y. P x y \<or> x = y) xm ym \<Longrightarrow>
   strict_subtuple (\<lambda>x y. P x y \<or> x = y)\<^sup>+\<^sup>+ ym zm \<Longrightarrow>
   strict_subtuple (\<lambda>x y. P x y \<or> x = y)\<^sup>+\<^sup>+ xm zm"
  apply auto
  apply (rule fmrel_on_fset_trans, auto)
  by (drule_tac ?xm="ym" in subtuple_acyclic'; auto)

lemma strict_subtuple_trans'':
  "acyclicP_on (fmran' zm) R \<Longrightarrow>
   strict_subtuple R xm ym \<Longrightarrow>
   strict_subtuple R\<^sup>*\<^sup>* ym zm \<Longrightarrow>
   strict_subtuple R\<^sup>*\<^sup>* xm zm"
  apply auto
  apply (rule fmrel_on_fset_trans, auto)
  by (drule_tac ?xm="ym" in subtuple_acyclic''; auto)

lemma strict_subtuple_trans''':
  "acyclicP_on (fmran' zm) P \<Longrightarrow>
   strict_subtuple (\<lambda>x y. P x y \<or> x = y) xm ym \<Longrightarrow>
   strict_subtuple (\<lambda>x y. P x y \<or> x = y)\<^sup>*\<^sup>* ym zm \<Longrightarrow>
   strict_subtuple (\<lambda>x y. P x y \<or> x = y)\<^sup>*\<^sup>* xm zm"
  apply auto
  apply (rule fmrel_on_fset_trans, auto)
  by (drule_tac ?xm="ym" in subtuple_acyclic'; auto)

lemma subtuple_fmmerge2 [intro]:
  "(\<And>x y. x \<in> fmran' xm \<Longrightarrow> f x (g x y)) \<Longrightarrow>
   subtuple f xm (fmmerge g xm ym)"
  by (rule_tac ?S="fmdom ym" in fmrel_on_fsubset; auto)

(*** Transitive Closures ****************************************************)

subsection \<open>Transitive Closures\<close>

lemma trancl_to_subtuple:
  "(subtuple r)\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   subtuple r\<^sup>+\<^sup>+ xm ym"
  apply (induct rule: tranclp_induct)
  apply (metis subtuple_mono tranclp.r_into_trancl)
  by (rule fmrel_on_fset_trans; auto)

lemma rtrancl_to_subtuple:
  "(subtuple r)\<^sup>*\<^sup>* xm ym \<Longrightarrow>
   subtuple r\<^sup>*\<^sup>* xm ym"
  apply (induct rule: rtranclp_induct)
  apply (simp add: fmap.rel_refl_strong fmrel_to_subtuple)
  by (rule fmrel_on_fset_trans; auto)

lemma fmrel_to_subtuple_trancl:
  "reflp r \<Longrightarrow>
   (fmrel r)\<^sup>+\<^sup>+ (fmrestrict_fset (fmdom ym) xm) ym \<Longrightarrow>
   (subtuple r)\<^sup>+\<^sup>+ xm ym"
  apply (frule trancl_to_fmrel)
  apply (rule_tac ?r="r" in fmrel_tranclp_induct, auto)
  apply (metis (no_types, lifting) fmrel_fmdom_eq
          subtuple_eq_fmrel_fmrestrict_fset tranclp.r_into_trancl)
  by (meson fmrel_to_subtuple tranclp.simps)

lemma subtuple_to_trancl:
  "reflp r \<Longrightarrow>
   subtuple r\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   (subtuple r)\<^sup>+\<^sup>+ xm ym"
  apply (rule fmrel_to_subtuple_trancl)
  unfolding fmrel_on_fset_fmrel_restrict
  by (simp_all add: fmrel_to_trancl)

lemma trancl_to_strict_subtuple:
  "acyclicP_on (fmran' ym) R \<Longrightarrow>
   (strict_subtuple R)\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   strict_subtuple R\<^sup>*\<^sup>* xm ym"
  apply (erule converse_tranclp_induct)
  apply (metis r_into_rtranclp strict_subtuple_mono)
  using strict_subtuple_trans'' by blast

lemma trancl_to_strict_subtuple':
  "acyclicP_on (fmran' ym) R \<Longrightarrow>
   (strict_subtuple (\<lambda>x y. R x y \<or> x = y))\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   strict_subtuple (\<lambda>x y. R x y \<or> x = y)\<^sup>*\<^sup>* xm ym"
  apply (erule converse_tranclp_induct)
  apply (metis (no_types, lifting) r_into_rtranclp strict_subtuple_mono)
  using strict_subtuple_trans''' by blast

lemma subtuple_rtranclp_intro:
  assumes "\<And>xm ym. R (f xm) (f ym) \<Longrightarrow> subtuple R xm ym"
      and "bij_on_trancl R f"
      and "R\<^sup>*\<^sup>* (f xm) (f ym)"
    shows "subtuple R\<^sup>*\<^sup>* xm ym"
proof -
  have "(\<lambda>xm ym. R (f xm) (f ym))\<^sup>*\<^sup>* xm ym"
    apply (insert assms(2) assms(3))
    by (rule reflect_rtranclp; auto)
  with assms(1) have "(subtuple R)\<^sup>*\<^sup>* xm ym"
    by (metis (mono_tags, lifting) mono_rtranclp)
  hence "subtuple R\<^sup>*\<^sup>* xm ym"
    by (rule rtrancl_to_subtuple)
  thus ?thesis by simp
qed

lemma strict_subtuple_rtranclp_intro:
  assumes "\<And>xm ym. R (f xm) (f ym) \<Longrightarrow>
           strict_subtuple (\<lambda>x y. R x y \<or> x = y) xm ym"
      and "bij_on_trancl R f"
      and "acyclicP_on (fmran' ym) R"
      and "R\<^sup>+\<^sup>+ (f xm) (f ym)"
    shows "strict_subtuple R\<^sup>*\<^sup>* xm ym"
proof -
  have "(\<lambda>xm ym. R (f xm) (f ym))\<^sup>+\<^sup>+ xm ym"
    apply (insert assms(1) assms(2) assms(4))
    by (rule reflect_tranclp; auto)
  hence "(strict_subtuple (\<lambda>x y. R x y \<or> x = y))\<^sup>+\<^sup>+ xm ym"
    by (rule tranclp_trans_induct;
        auto simp add: assms(1) tranclp.r_into_trancl)
  with assms(3) have "strict_subtuple (\<lambda>x y. R x y \<or> x = y)\<^sup>*\<^sup>* xm ym"
    by (rule trancl_to_strict_subtuple')
  thus ?thesis by simp
qed

(*** Code Setup *************************************************************)

subsection \<open>Code Setup\<close>

abbreviation "subtuple_fun f xm ym \<equiv>
  fBall (fmdom ym) (\<lambda>x. rel_option f (fmlookup xm x) (fmlookup ym x))"

abbreviation "strict_subtuple_fun f xm ym \<equiv>
  subtuple_fun f xm ym \<and> xm \<noteq> ym"

lemma subtuple_fun_simp [code_abbrev, simp]:
  "subtuple_fun f xm ym = subtuple f xm ym"
  by (simp add: fmrel_on_fset_alt_def)

lemma strict_subtuple_fun_simp [code_abbrev, simp]:
  "strict_subtuple_fun f xm ym = strict_subtuple f xm ym"
  by simp

end
