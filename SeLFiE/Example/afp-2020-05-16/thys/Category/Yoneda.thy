(*  Title:       Category theory using Isar and Locales
    Author:      Greg O'Keefe, June, July, August 2003
    License: LGPL
*)

section \<open>Yonedas Lemma\<close>

theory Yoneda
imports HomFunctors NatTrans
begin

subsection \<open>The Sandwich Natural Transformation\<close>

locale Yoneda = "functor" + into_set +
  assumes "TERM (AA :: ('o,'a,'m)category_scheme)"
  fixes sandwich :: "['o,'a,'o] \<Rightarrow> 'a set_arrow"  ("\<sigma>'(_,_')")
  defines "sandwich A a \<equiv> (\<lambda>B\<in>Ob. \<lparr>
  set_dom=Hom A B,
  set_func=(\<lambda>f\<in>Hom A B. set_func (F\<^bsub>\<a>\<^esub> f) a),
  set_cod=F\<^bsub>\<o>\<^esub> B
  \<rparr>)"
  fixes unsandwich :: "['o,'o \<Rightarrow> 'a set_arrow] \<Rightarrow> 'a" ("\<sigma>\<^sup>\<leftarrow>'(_,_')")
  defines "unsandwich A u \<equiv> set_func (u A) (Id A)"

lemma (in Yoneda) F_into_set: 
  "Functor F : AA \<longrightarrow> Set"
proof-
  from F_axioms have "Functor F : AA \<longrightarrow> BB" by intro_locales
  thus ?thesis
    by (simp only: BB_Set)
qed


lemma (in Yoneda) F_comp_func:
  assumes 1: "A \<in> Ob" and 2: "B \<in> Ob" and 3: "C \<in> Ob"
  and 4: "g \<in> Hom A B" and 5: "f \<in> Hom B C"
  shows "set_func (F\<^bsub>\<a>\<^esub> (f \<bullet> g)) = compose (F\<^bsub>\<o>\<^esub> A) (set_func (F\<^bsub>\<a>\<^esub> f)) (set_func (F\<^bsub>\<a>\<^esub> g))"
proof-
  from 4 and 5 
  have 7: "Cod g = Dom f" 
    and 8: "g \<in> Ar" 
    and 9: "f \<in> Ar"
    and 10: "Dom g = A"
    by (simp_all add: hom_def)
  from F_preserves_dom and 8 and 10
  have 11: "set_dom (F\<^bsub>\<a>\<^esub> g) = F\<^bsub>\<o>\<^esub> A"
    by (simp add: preserves_dom_def BB_Set Set_def) auto
  from F_preserves_comp and 7 and 8 and 9
  have "F\<^bsub>\<a>\<^esub> (f \<bullet> g) = (F\<^bsub>\<a>\<^esub> f) \<bullet>\<^bsub>BB\<^esub> (F\<^bsub>\<a>\<^esub> g)"
    by (simp add: preserves_comp_def)
  hence "set_func (F\<^bsub>\<a>\<^esub> (f \<bullet> g))  = set_func ((F\<^bsub>\<a>\<^esub> f) \<odot> (F\<^bsub>\<a>\<^esub> g))"
    by (simp add: BB_Set Set_def)
  also have "\<dots> = compose (F\<^bsub>\<o>\<^esub> A) (set_func (F\<^bsub>\<a>\<^esub> f)) (set_func (F\<^bsub>\<a>\<^esub> g))"
    by (simp add: set_comp_def 11)
  finally show ?thesis .
qed

lemma (in Yoneda) sandwich_funcset:
  assumes A: "A \<in> Ob"
  and "a \<in> F\<^bsub>\<o>\<^esub> A"
  shows  "\<sigma>(A,a) : Ob \<rightarrow> ar Set"
proof (rule funcsetI)
  fix B
  assume B: "B \<in> Ob"
  thus "\<sigma>(A,a) B \<in> ar Set"
  proof (simp add: Set_def sandwich_def set_cat_def)
    show "set_arrow U \<lparr>
      set_dom = Hom A B, 
      set_func = \<lambda>f\<in>Hom A B. set_func (F\<^bsub>\<a>\<^esub> f) a, 
      set_cod = F\<^bsub>\<o>\<^esub> B\<rparr>"
    proof (simp add: set_arrow_def, intro conjI)
      show "Hom A B \<subseteq> U" and "F\<^bsub>\<o>\<^esub> B \<subseteq> U"
        by (simp_all add: U_def)
      show "(\<lambda>f\<in>Hom A B. set_func (F\<^bsub>\<a>\<^esub> f) a) \<in> Hom A B \<rightarrow> F\<^bsub>\<o>\<^esub> B"
      proof (rule funcsetI, simp)
        fix f
        assume f: "f \<in> Hom A B"
        with A B have "F\<^bsub>\<a>\<^esub> f \<in> Hom\<^bsub>BB\<^esub> (F\<^bsub>\<o>\<^esub> A) (F\<^bsub>\<o>\<^esub> B)"
          by (rule functors_preserve_homsets)
        hence "F\<^bsub>\<a>\<^esub> f \<in> ar Set" 
          and "set_dom (F\<^bsub>\<a>\<^esub> f) = (F\<^bsub>\<o>\<^esub> A)"
          and "set_cod (F\<^bsub>\<a>\<^esub> f) = (F\<^bsub>\<o>\<^esub> B)"
          by (simp_all add: hom_def BB_Set Set_def)
        hence "set_func (F\<^bsub>\<a>\<^esub> f) : (F\<^bsub>\<o>\<^esub> A) \<rightarrow> (F\<^bsub>\<o>\<^esub> B)"
          by (simp add: Set_def set_cat_def set_arrow_def)
        thus "set_func (F\<^bsub>\<a>\<^esub> f) a \<in> F\<^bsub>\<o>\<^esub> B"
          using \<open>a \<in> F\<^bsub>\<o>\<^esub> A\<close>
          by (rule funcset_mem)
      qed
    qed
  qed
qed


lemma (in Yoneda) sandwich_type:
  assumes A: "A \<in> Ob" and B: "B \<in> Ob"
  and "a \<in> F\<^bsub>\<o>\<^esub> A"
  shows "\<sigma>(A,a) B \<in> hom Set (Hom A B) (F\<^bsub>\<o>\<^esub> B)"
proof-
  have "\<sigma>(A,a) \<in> Ob \<rightarrow> Ar\<^bsub>Set\<^esub>"
    using A and \<open>a \<in> F\<^bsub>\<o>\<^esub> A\<close> by (rule sandwich_funcset)
  hence "\<sigma>(A,a) B \<in> ar Set"
    using B by (rule funcset_mem)
  thus ?thesis
    using B by (simp add: sandwich_def hom_def Set_def)
qed


lemma (in Yoneda) sandwich_commutes:
  assumes AOb: "A \<in> Ob" and BOb: "B \<in> Ob" and COb: "C \<in> Ob"
  and aFa: "a \<in> F\<^bsub>\<o>\<^esub> A"
  and fBC: "f \<in> Hom B C"
  shows "(F\<^bsub>\<a>\<^esub> f) \<odot> (\<sigma>(A,a) B) = (\<sigma>(A,a) C) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f)"
proof-
  from fBC have 1: "f \<in> Ar" and 2: "Dom f = B" and 3: "Cod f = C"
    by (simp_all add: hom_def)
  from BOb have "set_dom ((F\<^bsub>\<a>\<^esub> f) \<odot> (\<sigma>(A,a) B)) = Hom A B"
    by (simp add: set_comp_def sandwich_def)
  also have "\<dots> = set_dom ((\<sigma>(A,a) C) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f))"
    by (simp add: set_comp_def homf_def 1 2)
  finally have set_dom_eq: 
    "set_dom ((F\<^bsub>\<a>\<^esub> f) \<odot> (\<sigma>(A,a) B)) 
    = set_dom ((\<sigma>(A,a) C) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f))" .
  from BOb COb fBC have "(F\<^bsub>\<a>\<^esub> f) \<in> Hom\<^bsub>BB\<^esub> (F\<^bsub>\<o>\<^esub> B) (F\<^bsub>\<o>\<^esub> C)" 
    by (rule functors_preserve_homsets)
  hence "set_cod ((F\<^bsub>\<a>\<^esub> f) \<odot> (\<sigma>(A,a) B)) = F\<^bsub>\<o>\<^esub> C"
    by (simp add: set_comp_def BB_Set Set_def set_cat_def hom_def)
  also from COb
  have "\<dots> = set_cod ((\<sigma>(A,a) C) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f))"
    by (simp add: set_comp_def sandwich_def)
  finally have set_cod_eq:
    "set_cod ((F\<^bsub>\<a>\<^esub> f) \<odot> (\<sigma>(A,a) B)) 
    = set_cod ((\<sigma>(A,a) C) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f))" .
  from AOb and BOb and COb and fBC and aFa
  have set_func_lhs: 
    "set_func ((F\<^bsub>\<a>\<^esub> f) \<odot> (\<sigma>(A,a) B)) = 
    (\<lambda>g\<in>Hom A B. set_func (F\<^bsub>\<a>\<^esub> (f \<bullet> g)) a)"
    apply (simp add:  set_comp_def sandwich_def compose_def)
    apply (rule extensionalityI, rule restrict_extensional, rule restrict_extensional)
    by (simp add: F_comp_func compose_def)
  have "(\<bullet>) : Hom B C \<rightarrow> Hom A B \<rightarrow> Hom A C" ..  
  from this and fBC 
  have opfType: "(\<bullet>) f : Hom A B \<rightarrow> Hom A C"
    by (rule funcset_mem)
  from 1 and 2
  have "set_func ((\<sigma>(A,a) C) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f)) =
    (\<lambda>g\<in>Hom A B. set_func (\<sigma>(A,a) C) (f \<bullet> g))"
    apply (simp add: set_comp_def homf_def)
    apply (simp add: compose_def)
    apply (rule extensionalityI, rule restrict_extensional, rule restrict_extensional)
    by auto
  also from COb and opfType 
  have " \<dots> = (\<lambda>g\<in>Hom A B. set_func (F\<^bsub>\<a>\<^esub> (f \<bullet> g)) a)"
    apply (simp add: sandwich_def)
    apply (rule extensionalityI, rule restrict_extensional, rule restrict_extensional)
    by (simp add:Pi_def)
  finally have set_func_rhs:
    "set_func ((\<sigma>(A,a) C) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f)) =
    (\<lambda>g\<in>Hom A B. set_func (F\<^bsub>\<a>\<^esub> (f \<bullet> g)) a)" .
  from set_func_lhs and set_func_rhs have
    "set_func ((F\<^bsub>\<a>\<^esub> f) \<odot> (\<sigma>(A,a) B))
    = set_func ((\<sigma>(A,a) C) \<odot> (Hom(A,_)\<^bsub>\<a>\<^esub> f))"
    by simp
  with set_dom_eq and set_cod_eq show ?thesis
    by simp
qed


lemma (in Yoneda) sandwich_natural:
  assumes "A \<in> Ob"
  and "a \<in> F\<^bsub>\<o>\<^esub> A"
  shows "\<sigma>(A,a) : Hom(A,_) \<Rightarrow> F in Func(AA,Set)"
proof (intro natural_transformation.intro natural_transformation_axioms.intro two_cats.intro)
  show "category AA" ..
  show "category Set" 
    by (simp only: Set_def)(rule set_cat_cat)
  show "Functor Hom(A,_) : AA \<longrightarrow> Set"
    by (rule homf_into_set)
  show "Functor F : AA \<longrightarrow> Set"
    by (rule F_into_set)
  show "\<forall>B\<in>Ob. \<sigma>(A,a) B \<in> hom Set (Hom(A,_)\<^bsub>\<o>\<^esub> B) (F\<^bsub>\<o>\<^esub> B)"
    using assms by (auto simp add: homf_def intro: sandwich_type)
  show "\<sigma>(A,a) : Ob \<rightarrow> ar Set"
    using assms by (rule sandwich_funcset)
  show "\<sigma>(A,a) \<in> extensional (Ob)"
    unfolding sandwich_def by (rule restrict_extensional)
  show "\<forall>B\<in>Ob. \<forall>C\<in>Ob. \<forall>f\<in>Hom B C.
    comp Set (F \<^bsub>\<a>\<^esub> f) (\<sigma>(A,a) B) = comp Set (\<sigma>(A,a) C) (Hom(A,_)\<^bsub>\<a>\<^esub> f)"
    using assms by (auto simp add: Set_def intro: sandwich_commutes)
qed


subsection \<open>Sandwich Components are Bijective\<close>

lemma (in Yoneda) unsandwich_left_inverse:
  assumes 1: "A \<in> Ob"
  and 2: "a \<in> F\<^bsub>\<o>\<^esub> A"
  shows "\<sigma>\<^sup>\<leftarrow>(A,\<sigma>(A,a)) = a"
proof-
  from 1 have "Id A \<in> Hom A A" ..
  with 1 
  have 3: "\<sigma>\<^sup>\<leftarrow>(A,\<sigma>(A,a)) = set_func (F\<^bsub>\<a>\<^esub> (Id A)) a"
    by (simp add: sandwich_def homf_def unsandwich_def)
  from F_preserves_id and 1
  have 4: "F\<^bsub>\<a>\<^esub> (Id A) = id Set (F\<^bsub>\<o>\<^esub> A)"
    by (simp add: preserves_id_def BB_Set)
  from F_preserves_objects and 1 
  have "F\<^bsub>\<o>\<^esub> A \<in> Ob\<^bsub>BB\<^esub>" 
    by (rule funcset_mem)
  hence "F\<^bsub>\<o>\<^esub> A \<subseteq> U"
    by (simp add: BB_Set Set_def set_cat_def)
  with 2
  have 5: "set_func (id Set (F\<^bsub>\<o>\<^esub> A)) a = a"
    by (simp add: Set_def  set_id_def)
  show ?thesis
    by (simp add: 3 4 5)
qed


lemma (in Yoneda) unsandwich_right_inverse:
  assumes 1: "A \<in> Ob"
  and 2: "u : Hom(A,_) \<Rightarrow> F in Func(AA,Set)"
  shows "\<sigma>(A,\<sigma>\<^sup>\<leftarrow>(A,u)) = u"
proof (rule extensionalityI)
  show "\<sigma>(A,\<sigma>\<^sup>\<leftarrow>(A,u)) \<in> extensional (Ob)"
    by (unfold sandwich_def, rule restrict_extensional)
  from 2 show "u \<in>  extensional (Ob)"
    by (simp add: natural_transformation_def natural_transformation_axioms_def)
  fix B
  assume 3: "B \<in> Ob"
  with 1
  have one: "\<sigma>(A,\<sigma>\<^sup>\<leftarrow>(A,u)) B = \<lparr>
    set_dom = Hom A B,
    set_func = (\<lambda>f\<in>Hom A B. (set_func (F\<^bsub>\<a>\<^esub> f)) (set_func (u A) (Id A))),
    set_cod = F\<^bsub>\<o>\<^esub> B \<rparr>"
    by (simp add: sandwich_def unsandwich_def)
  from 1 have "Hom(A,_)\<^bsub>\<o>\<^esub> A = Hom A A"
    by (simp add: homf_def)
  with 1 and 2 have "(u A) \<in> hom Set (Hom A A) (F\<^bsub>\<o>\<^esub> A)"
    by (simp add: natural_transformation_def natural_transformation_axioms_def,
      auto)
  hence "set_dom (u A) = Hom A A"
    by (simp add: hom_def Set_def)
  with 1 have applicable: "Id A \<in> set_dom (u A)"
    by (simp)(rule)
  have two: "(\<lambda>f\<in>Hom A B. (set_func (F\<^bsub>\<a>\<^esub> f)) (set_func (u A) (Id A))) 
    = (\<lambda>f\<in>Hom A B. (set_func ((F\<^bsub>\<a>\<^esub> f) \<odot> (u A)) (Id A)))" 
    by (rule extensionalityI,
      rule restrict_extensional, rule restrict_extensional,
      simp add: set_comp_def compose_def applicable)
  from 2
  have "(\<forall>X\<in>Ob. \<forall>Y\<in>Ob. \<forall>f\<in>Hom X Y. (F\<^bsub>\<a>\<^esub> f) \<bullet>\<^bsub>BB\<^esub> (u X) = (u Y) \<bullet>\<^bsub>BB\<^esub> (Hom(A,_)\<^bsub>\<a>\<^esub> f))"
    by (simp add: natural_transformation_def natural_transformation_axioms_def BB_Set)
  with 1 and 3 
  have three: "(\<lambda>f\<in>Hom A B. (set_func ((F\<^bsub>\<a>\<^esub> f) \<odot> (u A)) (Id A))) 
    = (\<lambda>f\<in>Hom A B. (set_func ((u B) \<odot> (Hom(A,_))\<^bsub>\<a>\<^esub> f)) (Id A))"
    apply (simp add: BB_Set Set_def)
    apply (rule extensionalityI)
    apply (rule restrict_extensional, rule restrict_extensional)
    by simp
  have "\<forall>f \<in> Hom A B. set_dom (Hom(A,_)\<^bsub>\<a>\<^esub> f) = Hom A A"
    by (intro ballI, simp add: homf_def hom_def)
  have roolz: "\<And>f. f \<in> Hom A B \<Longrightarrow> set_dom (Hom(A,_)\<^bsub>\<a>\<^esub> f) = Hom A A"
    by (simp add: homf_def hom_def)
  from 1 have rooly: "Id A \<in> Hom A A" ..
  have roolx: "\<And>f. f \<in> Hom A B \<Longrightarrow> f \<in> Ar"
    by (simp add: hom_def)
  have roolw: "\<And>f. f \<in> Hom A B \<Longrightarrow> Id A \<in> Hom A (Dom f)"
  proof-
    fix f
    assume "f \<in> Hom A B"
    hence "Dom f = A" by (simp add: hom_def)
    thus "Id A \<in> Hom A (Dom f)"
      by (simp add: rooly)
  qed
  have annoying: "\<And>f. f \<in> Hom A B \<Longrightarrow> Id A = Id (Dom f)"
    by (simp add: hom_def)
  have "(\<lambda>f\<in>Hom A B. (set_func ((u B) \<odot> (Hom(A,_))\<^bsub>\<a>\<^esub> f)) (Id A))
    = (\<lambda>f\<in>Hom A B. (compose (Hom A A) (set_func (u B)) (set_func (Hom(A,_)\<^bsub>\<a>\<^esub> f))) (Id A))"
    apply (rule extensionalityI)
    apply (rule restrict_extensional, rule restrict_extensional)
    by (simp add: compose_def set_comp_def roolz rooly)
  also have "\<dots> = (\<lambda>f\<in>Hom A B. (set_func (u B) f))"
    apply (rule extensionalityI)
    apply (rule restrict_extensional, rule restrict_extensional)
    apply (simp add: compose_def homf_def rooly roolx roolw)
    apply (simp only: annoying)
    apply (simp add: roolx id_right)
    done
  finally have four: 
    "(\<lambda>f\<in>Hom A B. (set_func ((u B) \<odot> (Hom(A,_))\<^bsub>\<a>\<^esub> f)) (Id A))
    = (\<lambda>f\<in>Hom A B. (set_func (u B) f))" .
  from 2 and  3 
  have uBhom: "u B \<in> hom Set (Hom(A,_)\<^bsub>\<o>\<^esub> B) (F\<^bsub>\<o>\<^esub> B)"
    by (simp add: natural_transformation_def natural_transformation_axioms_def)
  with 3 
  have five: "set_dom (u B) = Hom A B"
    by (simp add: hom_def homf_def Set_def set_cat_def)
  from uBhom
  have six: "set_cod (u B) = F\<^bsub>\<o>\<^esub> B" 
    by (simp add: hom_def homf_def Set_def set_cat_def)
  have seven: "restrict (set_func (u B)) (Hom A B) = set_func (u B)"
    apply (rule extensionalityI)
    apply (rule restrict_extensional)
  proof-
    from uBhom have "u B \<in> ar Set"
      by (simp add: hom_def)
    hence almost: "set_func (u B) \<in> extensional (set_dom (u B))"
      by (simp add: Set_def set_cat_def set_arrow_def)
    from almost and five
    show "set_func (u B) \<in> extensional (Hom A B)" 
      by simp
    fix f
    assume "f \<in> Hom A B"
    thus "restrict (set_func (u B)) (Hom A B) f = set_func (u B) f"
      by simp
  qed
  from one and two and three and four and five and six and seven
  show "\<sigma>(A,\<sigma>\<^sup>\<leftarrow>(A,u)) B = u B" 
    by simp
qed


text \<open>In order to state the lemma, we must rectify a curious
omission from the Isabelle/HOL library. They define the idea of
injectivity on a given set, but surjectivity is only defined relative
to the entire universe of the target type.\<close>

definition
  surj_on :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool" where
  "surj_on f A B \<longleftrightarrow> (\<forall>y\<in>B. \<exists>x\<in>A. f(x)=y)"

definition
  bij_on :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool" where
  "bij_on f A B \<longleftrightarrow> inj_on f A & surj_on f A B"

definition
  equinumerous :: "['a set, 'b set] \<Rightarrow> bool"  (infix "\<cong>" 40) where
  "equinumerous A B \<longleftrightarrow> (\<exists>f. bij_betw f A B)"

lemma bij_betw_eq:
  "bij_betw f A B \<longleftrightarrow>
    inj_on f A \<and> (\<forall>y\<in>B. \<exists>x\<in>A. f(x)=y) \<and> (\<forall>x\<in>A. f x \<in> B)"
unfolding bij_betw_def by auto

theorem (in Yoneda) Yoneda:
  assumes 1: "A \<in> Ob"
  shows "F\<^bsub>\<o>\<^esub> A \<cong> {u. u : Hom(A,_) \<Rightarrow> F in Func(AA,Set)}"
unfolding equinumerous_def bij_betw_eq inj_on_def
proof (intro exI conjI bexI ballI impI)
  \<comment> \<open>Sandwich is injective\<close>
  fix x and y
  assume 2: "x \<in> F\<^bsub>\<o>\<^esub> A" and 3: "y \<in> F\<^bsub>\<o>\<^esub> A"
  and 4: "\<sigma>(A,x) = \<sigma>(A,y)"
  hence "\<sigma>\<^sup>\<leftarrow>(A,\<sigma>(A,x)) = \<sigma>\<^sup>\<leftarrow>(A,\<sigma>(A,y))"
    by simp
  with unsandwich_left_inverse
  show "x = y"
    by (simp add: 1 2 3)
next
  \<comment> \<open>Sandwich covers F A\<close>
  fix u
  assume "u \<in> {y. y : Hom(A,_) \<Rightarrow> F in Func (AA,Set)}"
  hence 2: "u : Hom(A,_) \<Rightarrow> F in Func (AA,Set)"
    by simp
  with 1 show "\<sigma>(A,\<sigma>\<^sup>\<leftarrow>(A,u)) = u"
    by (rule unsandwich_right_inverse)
  \<comment> \<open>Sandwich is into F A\<close> (* there is really similar reasoning elsewhere*)
  from 1 and 2 
  have "u A \<in> hom Set (Hom A A) (F\<^bsub>\<o>\<^esub> A)"
    by (simp add: natural_transformation_def natural_transformation_axioms_def homf_def)
  hence "u A \<in> ar Set" and "dom Set (u A) = Hom A A" and "cod Set (u A) = F\<^bsub>\<o>\<^esub> A"
    by (simp_all add: hom_def)
  hence uAfuncset: "set_func (u A) : (Hom A A) \<rightarrow> (F\<^bsub>\<o>\<^esub> A)"
    by (simp add: Set_def set_cat_def set_arrow_def)
  from 1 have "Id A \<in> Hom A A" ..
  with uAfuncset 
  show "\<sigma>\<^sup>\<leftarrow>(A,u) \<in> F\<^bsub>\<o>\<^esub> A"
    by (simp add: unsandwich_def, rule funcset_mem)
next
  fix x
  assume "x \<in> F\<^bsub>\<o>\<^esub> A"
  with 1 have "\<sigma>(A,x) : Hom(A,_) \<Rightarrow> F in Func (AA,Set)"
    by (rule sandwich_natural)
  thus "\<sigma>(A,x) \<in> {y. y : Hom(A,_) \<Rightarrow> F in Func (AA,Set)}"
    by simp
qed

end
