(*  Title:       Category theory using Isar and Locales
    Author:      Greg O'Keefe, June, July, August 2003
    License: LGPL

Define homfunctors, prove that they are functors.
*)

section HomFunctors

theory HomFunctors
imports SetCat Functors
begin

locale into_set = two_cats AA BB
    for AA :: "('o,'a,'m)category_scheme" (structure)
    and BB (structure) +
  fixes U and Set 
  defines "U \<equiv> (UNIV::'a set)"
  defines "Set \<equiv> set_cat U"
  assumes BB_Set: "BB = Set"
  fixes homf ("Hom'(_,'_')")
  defines "homf A \<equiv> \<lparr>
  om = (\<lambda>B\<in>Ob. Hom A B),
  am = (\<lambda>f\<in>Ar. \<lparr>set_dom=Hom A (Dom f),set_func=(\<lambda>g\<in>Hom A (Dom f). f \<bullet> g),set_cod=Hom A (Cod f)\<rparr>)
  \<rparr>"


lemma (in into_set) homf_preserves_arrows:
 "Hom(A,_)\<^bsub>\<a>\<^esub> : Ar \<rightarrow> ar Set"
proof (rule funcsetI)
  fix f
  assume f: "f \<in> Ar"
  thus "Hom(A,_)\<^bsub>\<a>\<^esub> f \<in> ar Set"
  proof (simp add: homf_def Set_def set_cat_def set_arrow_def U_def)
    have 1: "(\<bullet>) : Hom (Dom f) (Cod f) \<rightarrow> Hom A (Dom f) \<rightarrow> Hom A (Cod f)" ..
    have 2: "f \<in> Hom (Dom f) (Cod f)" using f by (simp add: hom_def)
    from 1 and 2 have 3: "(\<bullet>) f : Hom A (Dom f) \<rightarrow> Hom A (Cod f)" 
      by (rule funcset_mem)
    show "(\<lambda>g\<in>Hom A (Dom f). f \<bullet> g) : Hom A (Dom f) \<rightarrow> Hom A (Cod f)"
    proof (rule funcsetI)
      fix g'
      assume "g' \<in> Hom A (Dom f)"
      from 3 and this show "(\<lambda>g\<in>Hom A (Dom f). f \<bullet> g) g' \<in> Hom A (Cod f)"
        by simp (rule funcset_mem)
    qed
  qed
qed


lemma (in into_set) homf_preserves_objects:
 "Hom(A,_)\<^bsub>\<o>\<^esub> : Ob \<rightarrow> ob Set"
proof (rule funcsetI)
  fix B
  assume B: "B \<in> Ob"
  have "Hom(A,_)\<^bsub>\<o>\<^esub> B = Hom A B"
    using B by (simp add: homf_def)
  moreover have "\<dots> \<in> ob Set"
    by (simp add: U_def Set_def set_cat_def)
  ultimately show "Hom(A,_)\<^bsub>\<o>\<^esub> B \<in> ob Set" by simp
qed


lemma (in into_set) homf_preserves_dom:
  assumes f: "f \<in> Ar"
  shows "Hom(A,_)\<^bsub>\<o>\<^esub> (Dom f) = dom Set (Hom(A,_)\<^bsub>\<a>\<^esub> f)"
proof-
  have "Dom f \<in> Ob" using f ..
  hence 1: "Hom(A,_)\<^bsub>\<o>\<^esub> (Dom f) = Hom A (Dom f)"
    using f by (simp add: homf_def)
  have 2: "dom Set (Hom(A,_)\<^bsub>\<a>\<^esub> f) = Hom A (Dom f)"
    using f by (simp add: Set_def homf_def)
  from 1 and 2 show ?thesis by simp
qed

lemma (in into_set) homf_preserves_cod:
  assumes f: "f \<in> Ar"
  shows "Hom(A,_)\<^bsub>\<o>\<^esub> (Cod f) = cod Set (Hom(A,_)\<^bsub>\<a>\<^esub> f)"
proof-
  have "Cod f \<in> Ob" using f ..
  hence 1: "Hom(A,_)\<^bsub>\<o>\<^esub> (Cod f) = Hom A (Cod f)"
    using f by (simp add: homf_def)
  have 2: "cod Set (Hom(A,_)\<^bsub>\<a>\<^esub> f) = Hom A (Cod f)"
    using f by (simp add: Set_def homf_def)
  from 1 and 2 show ?thesis by simp
qed


lemma (in into_set) homf_preserves_id:
  assumes B: "B \<in> Ob"
  shows "Hom(A,_)\<^bsub>\<a>\<^esub> (Id B) = id Set (Hom(A,_)\<^bsub>\<o>\<^esub> B)"
proof-
  have 1: "Id B \<in> Ar" using B ..
  have 2: "Dom (Id B) = B"
    using B by (rule AA.id_dom_cod)
  have 3: "Cod (Id B) = B"
    using B by (rule AA.id_dom_cod)
  have 4: "(\<lambda>g\<in>Hom A B. (Id B) \<bullet> g) = (\<lambda>g\<in>Hom A B. g)"
    by (rule ext) (auto simp add: hom_def)
  have "Hom(A,_)\<^bsub>\<a>\<^esub> (Id B) = \<lparr>
    set_dom=Hom A B, 
    set_func=(\<lambda>g\<in>Hom A B. g),
    set_cod=Hom A B\<rparr>"
    by (simp add: homf_def 1 2 3 4)
  also have "\<dots>= id Set (Hom(A,_)\<^bsub>\<o>\<^esub> B)"
    using B by (simp add: Set_def U_def set_cat_def set_id_def homf_def)
  finally show ?thesis .
qed
  

lemma (in into_set) homf_preserves_comp:
  assumes f: "f \<in> Ar" 
    and g: "g \<in> Ar"
    and fg: "Cod f = Dom g"
  shows "Hom(A,_)\<^bsub>\<a>\<^esub> (g \<bullet> f) = (Hom(A,_)\<^bsub>\<a>\<^esub> g) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f)"
proof-
  have 1: "g \<bullet> f \<in> Ar" using assms ..
  have 2: "Dom (g \<bullet> f) = Dom f" using f g fg ..
  have 3: "Cod (g \<bullet> f) = Cod g" using f g fg ..
  have lhs: "Hom(A,_)\<^bsub>\<a>\<^esub> (g \<bullet> f) = \<lparr>
    set_dom=Hom A (Dom f), 
    set_func=(\<lambda>h\<in>Hom A (Dom f). (g \<bullet> f) \<bullet> h),
    set_cod=Hom A (Cod g)\<rparr>"
    by (simp add: homf_def 1 2 3)
  have 4: "set_dom ((Hom(A,_)\<^bsub>\<a>\<^esub> g) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f)) = Hom A (Dom f)"
    using f by (simp add: set_comp_def homf_def)
  have 5: "set_cod ((Hom(A,_)\<^bsub>\<a>\<^esub> g) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f)) = Hom A (Cod g)"
    using g by (simp add: set_comp_def homf_def)
  have "set_func ((Hom(A,_)\<^bsub>\<a>\<^esub> g) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f))
      = compose (Hom A (Dom f)) (\<lambda>y\<in>Hom A (Dom g). g \<bullet> y) (\<lambda>x\<in>Hom A (Dom f). f \<bullet> x)"
    using f g by (simp add: set_comp_def homf_def)
  also have "\<dots> = (\<lambda>h\<in>Hom A (Dom f). (g \<bullet> f) \<bullet> h)"
  proof (
      rule extensionalityI, 
      rule compose_extensional,
      rule restrict_extensional,
      simp)
    fix h
    assume 10: "h \<in> Hom A (Dom f)"
    hence 11: "f \<bullet> h \<in> Hom A (Dom g)"
    proof-
      from 10 have "h \<in> Ar" by (simp add: hom_def)
      have 100: "(\<bullet>) : Hom (Dom f) (Dom g) \<rightarrow> Hom A (Dom f) \<rightarrow> Hom A (Dom g)"
        by (rule AA.comp_types)
      have "f \<in> Hom (Dom f) (Cod f)" using f by (simp add: hom_def)
      hence 101: "f \<in> Hom (Dom f) (Dom g)" using fg by simp
      from 100 and 101
      have "(\<bullet>) f : Hom A (Dom f) \<rightarrow> Hom A (Dom g)"
        by (rule funcset_mem)
      from this and 10 
      show "f \<bullet> h \<in> Hom A (Dom g)"
        by (rule funcset_mem)
    qed
    hence "Cod (f \<bullet> h) = Dom g" 
      and "Dom (f \<bullet> h) = A"
      and "f \<bullet> h \<in> Ar"
      by (simp_all add: hom_def)
    thus "compose (Hom A (Dom f)) (\<lambda>y\<in>Hom A (Dom g). g \<bullet> y) (\<lambda>x\<in>Hom A (Dom f). f \<bullet> x) h =
        (g \<bullet> f) \<bullet> h"
      using f g fg 10 by (simp add: compose_def 10 11 hom_def)
  qed
  finally have 6: "set_func ((Hom(A,_)\<^bsub>\<a>\<^esub> g) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f))
    = (\<lambda>h\<in>Hom A (Dom f). (g \<bullet> f) \<bullet> h)" .
  from 4 and 5 and 6
  have rhs: "(Hom(A,_)\<^bsub>\<a>\<^esub> g) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f) = \<lparr>
    set_dom=Hom A (Dom f), 
    set_func=(\<lambda>h\<in>Hom A (Dom f). (g \<bullet> f) \<bullet> h),
    set_cod=Hom A (Cod g)\<rparr>"
    by simp
  show ?thesis
    by (simp add: lhs rhs)
qed


theorem (in into_set) homf_into_set:
  "Functor Hom(A,_) : AA \<longrightarrow> Set"
proof (intro functor.intro functor_axioms.intro)
  show "Hom(A,_)\<^bsub>\<a>\<^esub> : Ar \<rightarrow> ar Set"
    by (rule homf_preserves_arrows)
  show "Hom(A,_)\<^bsub>\<o>\<^esub> : Ob \<rightarrow> ob Set"
    by (rule homf_preserves_objects)
  show "\<forall>f\<in>Ar. Hom(A,_)\<^bsub>\<o>\<^esub> (Dom f) = dom Set (Hom(A,_)\<^bsub>\<a>\<^esub> f)"
    by (intro ballI) (rule homf_preserves_dom)
  show "\<forall>f\<in>Ar. Hom(A,_)\<^bsub>\<o>\<^esub> (Cod f) = cod Set (Hom(A,_)\<^bsub>\<a>\<^esub> f)"
    by (intro ballI) (rule homf_preserves_cod)
  show "\<forall>B\<in>Ob. Hom(A,_)\<^bsub>\<a>\<^esub> (Id B) = id Set (Hom(A,_)\<^bsub>\<o>\<^esub> B)"
    by (intro ballI) (rule homf_preserves_id)
  show "\<forall>f\<in>Ar. \<forall>g\<in>Ar. 
    Cod f = Dom g \<longrightarrow>
    Hom(A,_)\<^bsub>\<a>\<^esub> (g \<bullet> f) = comp Set (Hom(A,_)\<^bsub>\<a>\<^esub> g) (Hom(A,_)\<^bsub>\<a>\<^esub> f)"
    by (intro ballI impI, simp add: Set_def set_cat_def) (rule homf_preserves_comp)
  show "two_cats AA Set"
  proof intro_locales
    show "category Set" 
      by (unfold Set_def, rule set_cat_cat)
  qed
qed

end
