(*  Title:       Category theory using Isar and Locales
    Author:      Greg O'Keefe, June, July, August 2003
    License: LGPL

Functors: Define functors and prove a trivial example.
*)

section \<open>Functors\<close>

theory Functors
imports Cat
begin

subsection \<open>Definitions\<close>

record ('o1,'a1,'o2,'a2) "functor" =
  om :: "'o1 \<Rightarrow> 'o2"
  am :: "'a1 \<Rightarrow> 'a2"

abbreviation
  om_syn  ("_ \<^bsub>\<o>\<^esub>" [81]) where
  "F\<^bsub>\<o>\<^esub> \<equiv> om F"

abbreviation
  am_syn  ("_ \<^bsub>\<a>\<^esub>" [81]) where
  "F\<^bsub>\<a>\<^esub> \<equiv> am F"

locale two_cats = AA?: category AA + BB?: category BB
    for AA :: "('o1,'a1,'m1)category_scheme" (structure)
    and BB :: "('o2,'a2,'m2)category_scheme" (structure) + 
  fixes preserves_dom  ::  "('o1,'a1,'o2,'a2)functor \<Rightarrow> bool"
    and preserves_cod  ::  "('o1,'a1,'o2,'a2)functor \<Rightarrow> bool"
    and preserves_id  ::  "('o1,'a1,'o2,'a2)functor \<Rightarrow> bool"
    and preserves_comp  ::  "('o1,'a1,'o2,'a2)functor \<Rightarrow> bool"
  defines "preserves_dom G \<equiv> \<forall>f\<in>Ar\<^bsub>AA\<^esub>. G\<^bsub>\<o>\<^esub> (Dom\<^bsub>AA\<^esub> f) = Dom\<^bsub>BB\<^esub> (G\<^bsub>\<a>\<^esub> f)"
    and "preserves_cod G \<equiv> \<forall>f\<in>Ar\<^bsub>AA\<^esub>. G\<^bsub>\<o>\<^esub> (Cod\<^bsub>AA\<^esub> f) = Cod\<^bsub>BB\<^esub> (G\<^bsub>\<a>\<^esub> f)"
    and "preserves_id G \<equiv> \<forall>A\<in>Ob\<^bsub>AA\<^esub>. G\<^bsub>\<a>\<^esub> (Id\<^bsub>AA\<^esub> A) = Id\<^bsub>BB\<^esub> (G\<^bsub>\<o>\<^esub> A)"
    and "preserves_comp G \<equiv>
      \<forall>f\<in>Ar\<^bsub>AA\<^esub>. \<forall>g\<in>Ar\<^bsub>AA\<^esub>. Cod\<^bsub>AA\<^esub> f = Dom\<^bsub>AA\<^esub> g \<longrightarrow> G\<^bsub>\<a>\<^esub> (g \<bullet>\<^bsub>AA\<^esub> f) = (G\<^bsub>\<a>\<^esub> g) \<bullet>\<^bsub>BB\<^esub> (G\<^bsub>\<a>\<^esub> f)"

locale "functor" = two_cats +
  fixes F (structure)
  assumes F_preserves_arrows: "F\<^bsub>\<a>\<^esub> : Ar\<^bsub>AA\<^esub> \<rightarrow> Ar\<^bsub>BB\<^esub>"
    and F_preserves_objects: "F\<^bsub>\<o>\<^esub> : Ob\<^bsub>AA\<^esub> \<rightarrow> Ob\<^bsub>BB\<^esub>"
    and F_preserves_dom: "preserves_dom F"
    and F_preserves_cod: "preserves_cod F"
    and F_preserves_id: "preserves_id F"
    and F_preserves_comp: "preserves_comp F"
begin

lemmas F_axioms = F_preserves_arrows F_preserves_objects F_preserves_dom 
  F_preserves_cod F_preserves_id F_preserves_comp

lemmas func_pred_defs = preserves_dom_def preserves_cod_def preserves_id_def preserves_comp_def

end

text \<open>This gives us nicer notation for asserting that things are functors.\<close>

abbreviation
  Functor  ("Functor _ : _ \<longrightarrow> _" [81]) where
  "Functor F : AA \<longrightarrow> BB \<equiv> functor AA BB F"


subsection \<open>Simple Lemmas\<close>

text \<open>For example:\<close>

lemma (in "functor") "Functor F : AA \<longrightarrow> BB" ..


lemma functors_preserve_arrows [intro]:
  assumes "Functor F : AA \<longrightarrow> BB"
    and "f \<in> ar AA"
  shows "F\<^bsub>\<a>\<^esub> f \<in> ar BB"
proof-
  from \<open>Functor F : AA \<longrightarrow> BB\<close>
  have "F\<^bsub>\<a>\<^esub> : ar AA \<rightarrow> ar BB"
    by (simp add: functor_def functor_axioms_def)
  from this and \<open>f \<in> ar AA\<close>
  show ?thesis by (rule funcset_mem)
qed


lemma (in "functor") functors_preserve_homsets:
  assumes 1: "A \<in> Ob\<^bsub>AA\<^esub>"
  and 2: "B \<in> Ob\<^bsub>AA\<^esub>"
  and 3: "f \<in> Hom\<^bsub>AA\<^esub> A B"
  shows "F\<^bsub>\<a>\<^esub> f \<in> Hom\<^bsub>BB\<^esub> (F\<^bsub>\<o>\<^esub> A) (F\<^bsub>\<o>\<^esub> B)"
proof-
  from 3 
  have 4: "f \<in> Ar" 
    by (simp add: hom_def)
  with F_preserves_arrows 
  have 5: "F\<^bsub>\<a>\<^esub> f \<in> Ar\<^bsub>BB\<^esub>" 
    by (rule funcset_mem)
  from 4 and F_preserves_dom 
  have "Dom\<^bsub>BB\<^esub> (F\<^bsub>\<a>\<^esub> f) = F\<^bsub>\<o>\<^esub> (Dom\<^bsub>AA\<^esub> f)"
    by (simp add: preserves_dom_def)
  also from 3 have "\<dots> = F\<^bsub>\<o>\<^esub> A"
    by (simp add: hom_def)
  finally have 6: "Dom\<^bsub>BB\<^esub> (F\<^bsub>\<a>\<^esub> f) = F\<^bsub>\<o>\<^esub> A" .
  from 4 and F_preserves_cod 
  have "Cod\<^bsub>BB\<^esub> (F\<^bsub>\<a>\<^esub> f) = F\<^bsub>\<o>\<^esub> (Cod\<^bsub>AA\<^esub> f)"
    by (simp add: preserves_cod_def)
  also from 3 have "\<dots> = F\<^bsub>\<o>\<^esub> B"
    by (simp add: hom_def)
  finally have 7: "Cod\<^bsub>BB\<^esub> (F\<^bsub>\<a>\<^esub> f) = F\<^bsub>\<o>\<^esub> B" .
  from 5 and 6 and 7
  show ?thesis
    by (simp add: hom_def)
qed
    

lemma functors_preserve_objects [intro]:
  assumes "Functor F : AA \<longrightarrow> BB"
    and "A \<in> ob AA"
  shows "F\<^bsub>\<o>\<^esub> A \<in> ob BB"
proof-
  from \<open>Functor F : AA \<longrightarrow> BB\<close>
  have "F\<^bsub>\<o>\<^esub> : ob AA \<rightarrow> ob BB"
    by (simp add: functor_def functor_axioms_def)
  from this and \<open>A \<in> ob AA\<close>
  show ?thesis by (rule funcset_mem)
qed


subsection \<open>Identity Functor\<close>

definition
  id_func :: "('o,'a,'m) category_scheme \<Rightarrow> ('o,'a,'o,'a) functor" where
  "id_func CC = \<lparr>om=(\<lambda>A\<in>ob CC. A), am=(\<lambda>f\<in>ar CC. f)\<rparr>"

locale one_cat = two_cats +
  assumes endo: "BB = AA"

lemma (in one_cat) id_func_preserves_arrows:
  shows "(id_func AA)\<^bsub>\<a>\<^esub> : Ar \<rightarrow> Ar"
  by (unfold id_func_def, rule funcsetI, simp)


lemma (in one_cat) id_func_preserves_objects:
  shows "(id_func AA)\<^bsub>\<o>\<^esub> : Ob \<rightarrow> Ob"
  by (unfold id_func_def, rule funcsetI, simp)


lemma (in one_cat) id_func_preserves_dom:
  shows  "preserves_dom (id_func AA)"
unfolding preserves_dom_def endo
proof
  fix f
  assume f: "f \<in> Ar"
  hence lhs: "(id_func AA)\<^bsub>\<o>\<^esub> (Dom f) = Dom f"
    by (simp add: id_func_def) auto
  have "(id_func AA)\<^bsub>\<a>\<^esub> f = f"
    using f by (simp add: id_func_def)
  hence rhs: "Dom (id_func AA)\<^bsub>\<a>\<^esub> f = Dom f"
    by simp
  from lhs and rhs show "(id_func AA)\<^bsub>\<o>\<^esub> (Dom f) = Dom (id_func AA)\<^bsub>\<a>\<^esub> f"
    by simp
qed

lemma (in one_cat) id_func_preserves_cod:
  "preserves_cod (id_func AA)"
apply (unfold preserves_cod_def, simp only: endo)
proof
  fix f
  assume f: "f \<in> Ar"
  hence lhs: "(id_func AA)\<^bsub>\<o>\<^esub> (Cod f) = Cod f"
    by (simp add: id_func_def) auto
  have "(id_func AA)\<^bsub>\<a>\<^esub> f = f"
    using f by (simp add: id_func_def)
  hence rhs: "Cod (id_func AA)\<^bsub>\<a>\<^esub> f = Cod f"
    by simp
  from lhs and rhs show "(id_func AA)\<^bsub>\<o>\<^esub> (Cod f) = Cod (id_func AA)\<^bsub>\<a>\<^esub> f"
    by simp
qed


lemma (in one_cat) id_func_preserves_id:
  "preserves_id (id_func AA)"
unfolding preserves_id_def endo
proof
  fix A
  assume A: "A \<in> Ob"
  hence lhs: "(id_func AA)\<^bsub>\<a>\<^esub> (Id A) = Id A"
    by (simp add: id_func_def) auto
  have "(id_func AA)\<^bsub>\<o>\<^esub> A = A"
    using A by (simp add: id_func_def)
  hence rhs: "Id ((id_func AA)\<^bsub>\<o>\<^esub> A) = Id A"
    by simp
  from lhs and rhs show "(id_func AA)\<^bsub>\<a>\<^esub> (Id A) = Id ((id_func AA)\<^bsub>\<o>\<^esub> A)"
    by simp
qed


lemma (in one_cat) id_func_preserves_comp:
  "preserves_comp (id_func AA)"
unfolding preserves_comp_def endo
proof (intro ballI impI)
  fix f and g
  assume f: "f \<in> Ar" and g: "g \<in> Ar" and "Cod f = Dom g"
  then have "g \<bullet> f \<in> Ar" ..
  hence lhs: "(id_func AA)\<^bsub>\<a>\<^esub> (g \<bullet> f) = g \<bullet> f"
    by (simp add: id_func_def)
  have id_f: "(id_func AA)\<^bsub>\<a>\<^esub> f = f"
    using f by (simp add: id_func_def)
  have id_g: "(id_func AA)\<^bsub>\<a>\<^esub> g = g"
    using g by (simp add: id_func_def)
  hence rhs: "(id_func AA)\<^bsub>\<a>\<^esub> g \<bullet> (id_func AA)\<^bsub>\<a>\<^esub> f = g \<bullet> f"
    by (simp add: id_f id_g)
  from lhs and rhs 
  show "(id_func AA)\<^bsub>\<a>\<^esub> (g \<bullet> f) = (id_func AA)\<^bsub>\<a>\<^esub> g \<bullet> (id_func AA)\<^bsub>\<a>\<^esub> f"
    by simp
qed

theorem (in one_cat) id_func_functor:
  "Functor (id_func AA) : AA \<longrightarrow> AA"
proof-
  from id_func_preserves_arrows
    and id_func_preserves_objects
    and id_func_preserves_dom
    and id_func_preserves_cod
    and id_func_preserves_id
    and id_func_preserves_comp
  show ?thesis
    by unfold_locales (simp_all add: endo preserves_dom_def
      preserves_cod_def preserves_id_def preserves_comp_def)
qed

end
