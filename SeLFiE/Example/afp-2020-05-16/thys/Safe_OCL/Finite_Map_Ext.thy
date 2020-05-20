(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
section \<open>Finite Maps\<close>
theory Finite_Map_Ext
  imports "HOL-Library.Finite_Map"
begin

type_notation fmap ("(_ \<rightharpoonup>\<^sub>f /_)" [22, 21] 21)

nonterminal fmaplets and fmaplet

syntax
  "_fmaplet"  :: "['a, 'a] \<Rightarrow> fmaplet"              ("_ /\<mapsto>\<^sub>f/ _")
  "_fmaplets" :: "['a, 'a] \<Rightarrow> fmaplet"              ("_ /[\<mapsto>\<^sub>f]/ _")
  ""          :: "fmaplet \<Rightarrow> fmaplets"              ("_")
  "_FMaplets" :: "[fmaplet, fmaplets] \<Rightarrow> fmaplets"  ("_,/ _")
  "_FMapUpd"  :: "['a \<rightharpoonup> 'b, fmaplets] \<Rightarrow> 'a \<rightharpoonup> 'b" ("_/'(_')" [900, 0] 900)
  "_FMap"     :: "fmaplets \<Rightarrow> 'a \<rightharpoonup> 'b"             ("(1[_])")

syntax (ASCII)
  "_fmaplet"  :: "['a, 'a] \<Rightarrow> fmaplet"              ("_ /|->f/ _")
  "_fmaplets" :: "['a, 'a] \<Rightarrow> fmaplet"              ("_ /[|->f]/ _")

translations
  "_FMapUpd m (_FMaplets xy ms)"      \<rightleftharpoons> "_FMapUpd (_FMapUpd m xy) ms"
  "_FMapUpd m (_fmaplet  x y)"        \<rightleftharpoons> "CONST fmupd x y m"
  "_FMap ms"                          \<rightleftharpoons> "_FMapUpd (CONST fmempty) ms"
  "_FMap (_FMaplets ms1 ms2)"         \<leftharpoondown> "_FMapUpd (_FMap ms1) ms2"
  "_FMaplets ms1 (_FMaplets ms2 ms3)" \<leftharpoondown> "_FMaplets (_FMaplets ms1 ms2) ms3"

(*** Helper Lemmas **********************************************************)

subsection \<open>Helper Lemmas\<close>

lemma fmrel_on_fset_fmdom:
  "fmrel_on_fset (fmdom ym) f xm ym \<Longrightarrow>
   k |\<in>| fmdom ym \<Longrightarrow>
   k |\<in>| fmdom xm"
  by (metis fmdom_notD fmdom_notI fmrel_on_fsetD option.rel_sel)

(*** Finite Map Merge *******************************************************)

subsection \<open>Merge Operation\<close>

definition "fmmerge f xm ym \<equiv>
  fmap_of_list (map
    (\<lambda>k. (k, f (the (fmlookup xm k)) (the (fmlookup ym k))))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))"

lemma fmdom_fmmerge [simp]:
  "fmdom (fmmerge g xm ym) = fmdom xm |\<inter>| fmdom ym"
  by (auto simp add: fmmerge_def fmdom_of_list)

lemma fmmerge_commut:
  assumes "\<And>x y. x \<in> fmran' xm \<Longrightarrow> f x y = f y x"
  shows "fmmerge f xm ym = fmmerge f ym xm"
proof -
  obtain zm where zm: "zm = sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)"
    by auto
  with assms have
    "map (\<lambda>k. (k, f (the (fmlookup xm k)) (the (fmlookup ym k)))) zm =
     map (\<lambda>k. (k, f (the (fmlookup ym k)) (the (fmlookup xm k)))) zm"
    by (auto) (metis fmdom_notI fmran'I notin_fset option.collapse)
  thus ?thesis
    unfolding fmmerge_def zm
    by (metis (no_types, lifting) inf_commute)
qed

lemma fmrel_on_fset_fmmerge1 [intro]:
  assumes "\<And>x y z. z \<in> fmran' zm \<Longrightarrow> f x z \<Longrightarrow> f y z \<Longrightarrow> f (g x y) z"
  assumes "fmrel_on_fset (fmdom zm) f xm zm"
  assumes "fmrel_on_fset (fmdom zm) f ym zm"
  shows "fmrel_on_fset (fmdom zm) f (fmmerge g xm ym) zm"
proof -
  {
    fix x a b c
    assume "x |\<in>| fmdom zm"
    moreover hence "x |\<in>| fmdom xm |\<inter>| fmdom ym"
      by (meson assms(2) assms(3) finterI fmrel_on_fset_fmdom)
    moreover assume "fmlookup xm x = Some a"
                and "fmlookup ym x = Some b"
                and "fmlookup zm x = Some c"
    moreover from assms calculation have "f (g a b) c"
      by (metis fmran'I fmrel_on_fsetD option.rel_inject(2))
    ultimately have
      "rel_option f (fmlookup (fmmerge g xm ym) x) (fmlookup zm x)"
      unfolding fmmerge_def fmlookup_of_list apply auto
      unfolding option_rel_Some2 apply (rule_tac ?x="g a b" in exI)
      unfolding map_of_map_restrict restrict_map_def
      by (auto simp: fmember.rep_eq)
  }
  with assms(2) assms(3) show ?thesis
    by (meson fmdomE fmrel_on_fsetI fmrel_on_fset_fmdom)
qed

lemma fmrel_on_fset_fmmerge2 [intro]:
  assumes "\<And>x y. x \<in> fmran' xm \<Longrightarrow> f x (g x y)"
  shows "fmrel_on_fset (fmdom ym) f xm (fmmerge g xm ym)"
proof -
  {
    fix x a b
    assume "x |\<in>| fmdom xm |\<inter>| fmdom ym"
       and "fmlookup xm x = Some a"
       and "fmlookup ym x = Some b"
    hence "rel_option f (fmlookup xm x) (fmlookup (fmmerge g xm ym) x)"
      unfolding fmmerge_def fmlookup_of_list apply auto
      unfolding option_rel_Some1 apply (rule_tac ?x="g a b" in exI)
      by (auto simp add: map_of_map_restrict fmember.rep_eq assms fmran'I)
  }
  with assms show ?thesis
    apply auto
    apply (rule fmrel_on_fsetI)
    by (metis (full_types) finterD1 fmdomE fmdom_fmmerge fmdom_notD rel_option_None2)
qed

(*** Acyclicity *************************************************************)

subsection \<open>Acyclicity\<close>

abbreviation "acyclic_on xs r \<equiv> (\<forall>x. x \<in> xs \<longrightarrow> (x, x) \<notin> r\<^sup>+)"

abbreviation "acyclicP_on xs r \<equiv> acyclic_on xs {(x, y). r x y}"

lemma fmrel_acyclic:
  "acyclicP_on (fmran' xm) R \<Longrightarrow>
   fmrel R\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel R ym xm \<Longrightarrow>
   xm = ym"
  by (metis (full_types) fmap_ext fmran'I fmrel_cases option.sel
        tranclp.trancl_into_trancl tranclp_unfold)

lemma fmrel_acyclic':
  assumes "acyclicP_on (fmran' ym) R"
  assumes "fmrel R\<^sup>+\<^sup>+ xm ym"
  assumes "fmrel R ym xm"
  shows "xm = ym"
proof -
  {
    fix x
    from assms(1) have
      "rel_option R\<^sup>+\<^sup>+ (fmlookup xm x) (fmlookup ym x) \<Longrightarrow>
       rel_option R (fmlookup ym x) (fmlookup xm x) \<Longrightarrow>
       rel_option R (fmlookup xm x) (fmlookup ym x)"
      by (metis (full_types) fmdom'_notD fmlookup_dom'_iff
            fmran'I option.rel_sel option.sel
            tranclp_into_tranclp2 tranclp_unfold)
  }
  with assms show ?thesis
    unfolding fmrel_iff
    by (metis fmap.rel_mono_strong fmrelI fmrel_acyclic tranclp.simps)
qed

lemma fmrel_on_fset_acyclic:
  "acyclicP_on (fmran' xm) R \<Longrightarrow>
   fmrel_on_fset (fmdom ym) R\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel_on_fset (fmdom xm) R ym xm \<Longrightarrow>
   xm = ym"
  unfolding fmrel_on_fset_fmrel_restrict
  by (metis (no_types, lifting) fmdom_filter fmfilter_alt_defs(5)
        fmfilter_cong fmlookup_filter fmrel_acyclic fmrel_fmdom_eq
        fmrestrict_fset_dom option.simps(3))

lemma fmrel_on_fset_acyclic':
  "acyclicP_on (fmran' ym) R \<Longrightarrow>
   fmrel_on_fset (fmdom ym) R\<^sup>+\<^sup>+ xm ym \<Longrightarrow>
   fmrel_on_fset (fmdom xm) R ym xm \<Longrightarrow>
   xm = ym"
  unfolding fmrel_on_fset_fmrel_restrict
  by (metis (no_types, lifting) ffmember_filter fmdom_filter
        fmfilter_alt_defs(5) fmfilter_cong fmrel_acyclic'
        fmrel_fmdom_eq fmrestrict_fset_dom)

(*** Transitive Closures ****************************************************)

subsection \<open>Transitive Closures\<close>

lemma fmrel_trans:
  "(\<And>x y z. x \<in> fmran' xm \<Longrightarrow> P x y \<Longrightarrow> Q y z \<Longrightarrow> R x z) \<Longrightarrow>
   fmrel P xm ym \<Longrightarrow> fmrel Q ym zm \<Longrightarrow> fmrel R xm zm"
  unfolding fmrel_iff
  by (metis fmdomE fmdom_notD fmran'I option.rel_inject(2) option.rel_sel)

lemma fmrel_on_fset_trans:
  "(\<And>x y z. x \<in> fmran' xm \<Longrightarrow> P x y \<Longrightarrow> Q y z \<Longrightarrow> R x z) \<Longrightarrow>
   fmrel_on_fset (fmdom ym) P xm ym \<Longrightarrow>
   fmrel_on_fset (fmdom zm) Q ym zm \<Longrightarrow>
   fmrel_on_fset (fmdom zm) R xm zm"
  apply (rule fmrel_on_fsetI)
  unfolding option.rel_sel apply auto
  apply (meson fmdom_notI fmrel_on_fset_fmdom)
  by (metis fmdom_notI fmran'I fmrel_on_fsetD fmrel_on_fset_fmdom
            option.rel_sel option.sel)

lemma trancl_to_fmrel:
  "(fmrel f)\<^sup>+\<^sup>+ xm ym \<Longrightarrow> fmrel f\<^sup>+\<^sup>+ xm ym"
  apply (induct rule: tranclp_induct)
  apply (simp add: fmap.rel_mono_strong)
  by (rule fmrel_trans; auto)

lemma fmrel_trancl_fmdom_eq:
  "(fmrel f)\<^sup>+\<^sup>+ xm ym \<Longrightarrow> fmdom xm = fmdom ym"
  by (induct rule: tranclp_induct; simp add: fmrel_fmdom_eq)

text \<open>
  The proof was derived from the accepted answer on the website
  Stack Overflow that is available at
  @{url "https://stackoverflow.com/a/53585232/632199"}
  and provided with the permission of the author of the answer.\<close>

lemma fmupd_fmdrop:
  "fmlookup xm k = Some x \<Longrightarrow>
   xm = fmupd k x (fmdrop k xm)"
  apply (rule fmap_ext)
  unfolding fmlookup_drop fmupd_lookup
  by auto

lemma fmap_eqdom_Cons1:
  assumes "fmlookup xm i = None"
      and "fmdom (fmupd i x xm) = fmdom ym"
      and "fmrel R (fmupd i x xm) ym"
    shows "(\<exists>z zm. fmlookup zm i = None \<and> ym = (fmupd i z zm) \<and>
                   R x z \<and> fmrel R xm zm)"
proof -
  from assms(2) obtain y where "fmlookup ym i = Some y" by force
  then obtain z zm where z_zm: "ym = fmupd i z zm \<and> fmlookup zm i = None"
    using fmupd_fmdrop by force
  {
    assume "\<not> R x z"
    with z_zm have "\<not> fmrel R (fmupd i x xm) ym"
      by (metis fmrel_iff fmupd_lookup option.simps(11))
  }
  with assms(3) moreover have "R x z" by auto
  {
    assume "\<not> fmrel R xm zm"
    with assms(1) have "\<not> fmrel R (fmupd i x xm) ym"
      by (metis fmrel_iff fmupd_lookup option.rel_sel z_zm)
  }
  with assms(3) moreover have "fmrel R xm zm" by auto
  ultimately show ?thesis using z_zm by blast
qed

text \<open>
  The proof was derived from the accepted answer on the website
  Stack Overflow that is available at
  @{url "https://stackoverflow.com/a/53585232/632199"}
  and provided with the permission of the author of the answer.\<close>

lemma fmap_eqdom_induct [consumes 2, case_names nil step]:
  assumes R: "fmrel R xm ym"
    and dom_eq: "fmdom xm = fmdom ym"
    and nil: "P (fmap_of_list []) (fmap_of_list [])"
    and step:
    "\<And>x xm y ym i.
    \<lbrakk>R x y; fmrel R xm ym; fmdom xm = fmdom ym; P xm ym\<rbrakk> \<Longrightarrow>
    P (fmupd i x xm) (fmupd i y ym)"
  shows "P xm ym"
  using R dom_eq
proof (induct xm arbitrary: ym)
  case fmempty thus ?case
    by (metis fempty_iff fmdom_empty fmempty_of_list fmfilter_alt_defs(5)
              fmfilter_false fmrestrict_fset_dom local.nil)
next
  case (fmupd i x xm) show ?case
  proof -
    obtain y where "fmlookup ym i = Some y"
      by (metis fmupd.prems(1) fmrel_cases fmupd_lookup option.discI)
    from fmupd.hyps(2) fmupd.prems(1) fmupd.prems(2) obtain z zm where
      "fmlookup zm i = None" and
      ym_eq_z_zm: "ym = (fmupd i z zm)" and
      R_x_z: "R x z" and
      R_xm_zm: "fmrel R xm zm"
      using fmap_eqdom_Cons1 by metis
    hence dom_xm_eq_dom_zm: "fmdom xm = fmdom zm"
      using fmrel_fmdom_eq by blast
    with R_xm_zm fmupd.hyps(1) have "P xm zm" by blast
    with R_x_z R_xm_zm dom_xm_eq_dom_zm have
      "P (fmupd i x xm) (fmupd i z zm)"
      by (rule step)
    thus ?thesis by (simp add: ym_eq_z_zm)
  qed
qed

text \<open>
  The proof was derived from the accepted answer on the website
  Stack Overflow that is available at
  @{url "https://stackoverflow.com/a/53585232/632199"}
  and provided with the permission of the author of the answer.\<close>

lemma fmrel_to_rtrancl:
  assumes as_r: "reflp r"
      and rel_rpp_xm_ym: "fmrel r\<^sup>*\<^sup>* xm ym"
    shows "(fmrel r)\<^sup>*\<^sup>* xm ym"
proof -
  from rel_rpp_xm_ym have "fmdom xm = fmdom ym"
    using fmrel_fmdom_eq by blast
  with rel_rpp_xm_ym show "(fmrel r)\<^sup>*\<^sup>* xm ym"
  proof (induct rule: fmap_eqdom_induct)
    case nil show ?case by auto
  next
    case (step x xm y ym i) show ?case
    proof -
      from step.hyps(1) have "(fmrel r)\<^sup>*\<^sup>* (fmupd i x xm) (fmupd i y xm)"
      proof (induct rule: rtranclp_induct)
        case base show ?case by simp
      next
        case (step y z) show ?case
        proof -
          from as_r have "fmrel r xm xm"
            by (simp add: fmap.rel_reflp reflpD)
          with step.hyps(2) have "(fmrel r)\<^sup>*\<^sup>* (fmupd i y xm) (fmupd i z xm)"
            by (simp add: fmrel_upd r_into_rtranclp)
          with step.hyps(3) show ?thesis by simp
        qed
      qed
      also from step.hyps(4) have "(fmrel r)\<^sup>*\<^sup>* (fmupd i y xm) (fmupd i y ym)"
      proof (induct rule: rtranclp_induct)
        case base show ?case by simp
      next
        case (step ya za) show ?case
        proof -
          from step.hyps(2) as_r have "(fmrel r)\<^sup>*\<^sup>* (fmupd i y ya) (fmupd i y za)"
            by (simp add: fmrel_upd r_into_rtranclp reflp_def)
          with step.hyps(3) show ?thesis by simp
        qed
      qed
      finally show ?thesis by simp
    qed
  qed
qed

text \<open>
  The proof was derived from the accepted answer on the website
  Stack Overflow that is available at
  @{url "https://stackoverflow.com/a/53585232/632199"}
  and provided with the permission of the author of the answer.\<close>

lemma fmrel_to_trancl:
  assumes "reflp r"
      and "fmrel r\<^sup>+\<^sup>+ xm ym"
    shows "(fmrel r)\<^sup>+\<^sup>+ xm ym"
proof -
  from assms(2) have "fmrel r\<^sup>*\<^sup>* xm ym"
    by (drule_tac ?Ra="r\<^sup>*\<^sup>*" in fmap.rel_mono_strong; auto)
  with assms(1) have "(fmrel r)\<^sup>*\<^sup>* xm ym"
    by (simp add: fmrel_to_rtrancl)
  with assms(1) show ?thesis
    by (metis fmap.rel_reflp reflpD rtranclpD tranclp.r_into_trancl)
qed

lemma fmrel_tranclp_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   reflp r \<Longrightarrow>
   (\<And>y. fmrel r a y \<Longrightarrow> P y) \<Longrightarrow>
   (\<And>y z. (fmrel r)\<^sup>+\<^sup>+ a y \<Longrightarrow> fmrel r y z \<Longrightarrow> P y \<Longrightarrow> P z) \<Longrightarrow> P b"
  apply (drule fmrel_to_trancl, simp)
  by (erule tranclp_induct; simp)

lemma fmrel_converse_tranclp_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   reflp r \<Longrightarrow>
   (\<And>y. fmrel r y b \<Longrightarrow> P y) \<Longrightarrow>
   (\<And>y z. fmrel r y z \<Longrightarrow> fmrel r\<^sup>+\<^sup>+ z b \<Longrightarrow> P z \<Longrightarrow> P y) \<Longrightarrow> P a"
  apply (drule fmrel_to_trancl, simp)
  by (erule converse_tranclp_induct; simp add: trancl_to_fmrel)

lemma fmrel_tranclp_trans_induct:
  "fmrel r\<^sup>+\<^sup>+ a b \<Longrightarrow>
   reflp r \<Longrightarrow>
   (\<And>x y. fmrel r x y \<Longrightarrow> P x y) \<Longrightarrow>
   (\<And>x y z. fmrel r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> fmrel r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z) \<Longrightarrow>
   P a b"
  apply (drule fmrel_to_trancl, simp)
  apply (erule tranclp_trans_induct, simp)
  using trancl_to_fmrel by blast

(*** Finite Map Size Calculation ********************************************)

subsection \<open>Size Calculation\<close>

text \<open>
  The contents of the subsection was derived from the accepted answer
  on the website Stack Overflow that is available at
  @{url "https://stackoverflow.com/a/53244203/632199"}
  and provided with the permission of the author of the answer.\<close>

abbreviation "tcf \<equiv> (\<lambda> v::('a \<times> nat). (\<lambda> r::nat. snd v + r))"

interpretation tcf: comp_fun_commute tcf
proof
  fix x y :: "'a \<times> nat"
  show "tcf y \<circ> tcf x = tcf x \<circ> tcf y"
  proof -
    fix z
    have "(tcf y \<circ> tcf x) z = snd y + snd x + z" by auto
    also have "(tcf x \<circ> tcf y) z = snd y + snd x + z" by auto
    finally have "(tcf y \<circ> tcf x) z = (tcf x \<circ> tcf y) z" by auto
    thus "(tcf y \<circ> tcf x) = (tcf x \<circ> tcf y)" by auto
  qed
qed

lemma ffold_rec_exp:
  assumes "k |\<in>| fmdom x"
    and "ky = (k, the (fmlookup (fmmap f x) k))"
  shows "ffold tcf 0 (fset_of_fmap (fmmap f x)) =
        tcf ky (ffold tcf 0 ((fset_of_fmap (fmmap f x)) |-| {|ky|}))"
proof -
  have "ky |\<in>| (fset_of_fmap (fmmap f x))"
    using assms by auto
  thus ?thesis
    by (simp add: tcf.ffold_rec)
qed

lemma elem_le_ffold [intro]:
  "k |\<in>| fmdom x \<Longrightarrow>
   f (the (fmlookup x k)) < Suc (ffold tcf 0 (fset_of_fmap (fmmap f x)))"
  by (subst ffold_rec_exp, auto)

lemma elem_le_ffold' [intro]:
  "z \<in> fmran' x \<Longrightarrow>
   f z < Suc (ffold tcf 0 (fset_of_fmap (fmmap f x)))"
  apply (erule fmran'E)
  apply (frule fmdomI)
  by (subst ffold_rec_exp, auto)

(*** Code Setup *************************************************************)

subsection \<open>Code Setup\<close>

abbreviation "fmmerge_fun f xm ym \<equiv>
  fmap_of_list (map
    (\<lambda>k. if k |\<in>| fmdom xm \<and> k |\<in>| fmdom ym
         then (k, f (the (fmlookup xm k)) (the (fmlookup ym k)))
         else (k, undefined))
    (sorted_list_of_fset (fmdom xm |\<inter>| fmdom ym)))"

lemma fmmerge_fun_simp [code_abbrev, simp]:
  "fmmerge_fun f xm ym = fmmerge f xm ym"
  unfolding fmmerge_def
  apply (rule_tac ?f="fmap_of_list" in HOL.arg_cong)
  by (simp add: notin_fset)

end
