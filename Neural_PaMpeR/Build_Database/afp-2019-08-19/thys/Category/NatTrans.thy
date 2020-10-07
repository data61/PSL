(*  Title:       Category theory using Isar and Locales
    Author:      Greg O'Keefe, June, July, August 2003
    License: LGPL

Define natural transformation, prove that the identity arrow function is one.
*)

section \<open>Natural Transformations\<close>

theory NatTrans
imports Functors
begin

(* guess the third axiom is implied by the fifth *)
locale natural_transformation = two_cats +
  fixes F and G and u
  assumes "Functor F : AA \<longrightarrow> BB"
  and "Functor G : AA \<longrightarrow> BB"
  and "u : ob AA \<rightarrow> ar BB"
  and "u \<in> extensional (ob AA)"
  and "\<forall>A\<in>Ob. u A \<in> Hom\<^bsub>BB\<^esub> (F\<^bsub>\<o>\<^esub> A) (G\<^bsub>\<o>\<^esub> A)" 
  and "\<forall>A\<in>Ob. \<forall>B\<in>Ob. \<forall>f\<in>Hom A B. (G\<^bsub>\<a>\<^esub> f) \<bullet>\<^bsub>BB\<^esub> (u A) = (u B) \<bullet>\<^bsub>BB\<^esub> (F\<^bsub>\<a>\<^esub> f)"

abbreviation
  nt_syn  ("_ : _ \<Rightarrow> _ in Func '(_ , _ ')" [81]) where
  "u : F \<Rightarrow> G in Func(AA, BB) \<equiv> natural_transformation AA BB F G u"

(* is this doing what I think its doing? *)
locale endoNT = natural_transformation + one_cat

theorem (in endoNT) id_restrict_natural:
  "(\<lambda>A\<in>Ob. Id A) : (id_func AA) \<Rightarrow> (id_func AA) in Func(AA,AA)"
proof (intro natural_transformation.intro natural_transformation_axioms.intro 
    two_cats.intro ballI)
  show "(\<lambda>A\<in>Ob. Id A) : Ob \<rightarrow> Ar"
    by (rule funcsetI) auto
  show "(\<lambda>A\<in>Ob. Id A) \<in> extensional (Ob)"
    by (rule restrict_extensional)
  fix A 
  assume A: "A \<in> Ob" 
  hence "Id A \<in> Hom A A" ..
  thus "(\<lambda>X\<in>Ob. Id X) A \<in> Hom ((id_func AA)\<^bsub>\<o>\<^esub> A)  ((id_func AA)\<^bsub>\<o>\<^esub> A)"
    using A by (simp add: id_func_def) 
  fix B and f
  assume B: "B \<in> Ob" 
    and "f \<in> Hom A B"
  hence "f \<in> Ar" and "A = Dom f" and "B = Cod f" and "Dom f \<in> Ob" and "Cod f \<in> Ob"
    using A by (simp_all add: hom_def)
  thus "(id_func AA)\<^bsub>\<a>\<^esub> f \<bullet> (\<lambda>A\<in>Ob. Id A) A
      = (\<lambda>A\<in>Ob. Id A) B \<bullet> (id_func AA)\<^bsub>\<a>\<^esub> f"
    by (simp add:  id_func_def)
qed (auto intro: id_func_functor, unfold_locales, unfold_locales)

end
