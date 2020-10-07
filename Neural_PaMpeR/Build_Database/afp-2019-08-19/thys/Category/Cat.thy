(*  Title:       Category theory using Isar and Locales
    Author:      Greg O'Keefe, June, July, August 2003
    License: LGPL
*)

section \<open>Categories\<close>

theory Cat
imports "HOL-Library.FuncSet"
begin

subsection \<open>Definitions\<close>

record ('o, 'a) category =
  ob :: "'o set" ("Ob\<index>"  70)
  ar :: "'a set" ("Ar\<index>"  70)
  dom :: "'a \<Rightarrow> 'o" ("Dom\<index> _" [81] 70)
  cod :: "'a \<Rightarrow> 'o" ("Cod\<index> _" [81] 70)
  id :: "'o \<Rightarrow> 'a" ("Id\<index> _" [81] 80)
  comp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<bullet>\<index>" 60)

definition
  hom :: "[('o,'a,'m) category_scheme, 'o, 'o] \<Rightarrow> 'a set"
    ("Hom\<index> _ _" [81,81] 80) where
  "hom CC A B = { f. f\<in>ar CC & dom CC f = A & cod CC f = B }"

locale category =
  fixes CC (structure)
  assumes dom_object [intro]:
  "f \<in> Ar \<Longrightarrow> Dom f \<in> Ob"
  and cod_object [intro]:
  "f \<in> Ar \<Longrightarrow> Cod f \<in> Ob"
  and id_left [simp]:
  "f \<in> Ar \<Longrightarrow> Id (Cod f) \<bullet> f = f"
  and id_right [simp]:
  "f \<in> Ar \<Longrightarrow> f \<bullet> Id (Dom f) = f"
  and id_hom [intro]:
  "A \<in> Ob \<Longrightarrow> Id A \<in> Hom A A"
  and comp_types [intro]:
  "\<And>A B C. (comp CC) : (Hom B C) \<rightarrow> (Hom A B) \<rightarrow> (Hom A C)"
  and comp_associative [simp]:
  "f \<in> Ar \<Longrightarrow> g \<in> Ar \<Longrightarrow> h \<in> Ar
  \<Longrightarrow> Cod h = Dom g \<Longrightarrow> Cod g = Dom f
  \<Longrightarrow> f \<bullet> (g \<bullet> h) = (f \<bullet> g) \<bullet> h"


subsection \<open>Lemmas\<close>

lemma (in category) homI:
  assumes "f \<in> Ar" and "Dom f = A" and "Cod f = B"
  shows "f \<in> Hom A B"
  using assms by (auto simp add: hom_def)

lemma (in category) homE:
  assumes "A \<in> Ob" and "B \<in> Ob" and "f \<in> Hom A B"
  shows "Dom f = A" and "Cod f = B"
proof-
  show "Dom f = A" using assms by (simp add: hom_def) 
  show "Cod f = B" using assms by (simp add: hom_def) 
qed
   
lemma (in category) id_arrow [intro]:
  assumes "A \<in> Ob"
  shows "Id A \<in> Ar"
proof-
  from \<open>A \<in> Ob\<close> have "Id A \<in> Hom A A" by (rule id_hom)
  thus "Id A \<in> Ar" by (simp add: hom_def)
qed

lemma (in category) id_dom_cod:
  assumes "A \<in> Ob"
  shows "Dom (Id A) = A" and "Cod (Id A) = A"
proof-
  from \<open>A \<in> Ob\<close> have 1: "Id A \<in> Hom A A" ..
  then show "Dom (Id A) = A" and "Cod (Id A) = A"
    by (simp_all add: hom_def)
qed


lemma (in category) compI [intro]:
  assumes f: "f \<in> Ar" and g: "g \<in> Ar" and "Cod f = Dom g"
  shows "g \<bullet> f \<in> Ar"
  and "Dom (g \<bullet> f) = Dom f"
  and "Cod (g \<bullet> f) = Cod g"
proof-
  have "f \<in> Hom (Dom f) (Cod f)" using f by (simp add: hom_def)
  with \<open>Cod f = Dom g\<close> have f_homset: "f \<in> Hom (Dom f) (Dom g)" by simp
  have g_homset: "g \<in> Hom (Dom g) (Cod g)" using g by (simp add: hom_def)
  have "(\<bullet>) : Hom (Dom g) (Cod g) \<rightarrow> Hom (Dom f) (Dom g) \<rightarrow> Hom (Dom f) (Cod g)" ..
  from this and g_homset 
  have "(\<bullet>) g \<in> Hom (Dom f) (Dom g) \<rightarrow> Hom (Dom f) (Cod g)" 
    by (rule funcset_mem)
  from this and f_homset 
  have gf_homset: "g \<bullet> f \<in> Hom (Dom f) (Cod g)"
    by (rule funcset_mem)
  thus "g \<bullet> f \<in> Ar"
    by (simp add: hom_def) 
  from gf_homset show "Dom (g \<bullet> f) = Dom f" and "Cod (g \<bullet> f) = Cod g"
    by (simp_all add: hom_def)
qed

end
