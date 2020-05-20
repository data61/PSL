section {* Some preliminaries on equivalence relations and quotients *}

theory Equiv_Relation2 imports Preliminaries Pick
begin


text{* Unary predicates vs. sets: *}

definition "S2P A \<equiv> \<lambda> x. x \<in> A"

lemma S2P_app[simp]: "S2P r x \<longleftrightarrow> x \<in> r"
unfolding S2P_def by auto

lemma S2P_Collect[simp]: "S2P (Collect \<phi>) = \<phi>"
apply(rule ext)+ by simp

lemma Collect_S2P[simp]: "Collect (S2P r) = r"
by (metis Collect_mem_eq S2P_Collect)


text{* Binary predicates vs. relatipons: *}
definition "P2R \<phi> \<equiv> {(x,y). \<phi> x y}"
definition "R2P r \<equiv> \<lambda> x y. (x,y) \<in> r"

lemma in_P2R[simp]: "xy \<in> P2R \<phi> \<longleftrightarrow> \<phi> (fst xy) (snd xy)"
unfolding P2R_def by auto

lemma in_P2R_pair[simp]: "(x,y) \<in> P2R \<phi> \<longleftrightarrow> \<phi> x y"
by simp

lemma R2P_app[simp]: "R2P r x y \<longleftrightarrow> (x,y) \<in> r"
unfolding R2P_def by auto

lemma R2P_P2R[simp]: "R2P (P2R \<phi>) = \<phi>"
apply(rule ext)+ by simp

lemma P2R_R2P[simp]: "P2R (R2P r) = r"
using Collect_mem_eq P2R_def R2P_P2R  case_prod_curry by metis

definition "reflP P \<phi> \<equiv> (\<forall> x y. \<phi> x y \<or> \<phi> y x \<longrightarrow> P x) \<and> (\<forall> x. P x \<longrightarrow> \<phi> x x)"
definition "symP \<phi> \<equiv> \<forall> x y. \<phi> x y \<longrightarrow> \<phi> y x"
definition transP where "transP \<phi> \<equiv> \<forall> x y z. \<phi> x y \<and> \<phi> y z \<longrightarrow> \<phi> x z"
definition "equivP A \<phi> \<equiv> reflP A \<phi> \<and> symP \<phi> \<and> transP \<phi>"

lemma refl_on_P2R[simp]: "refl_on (Collect P) (P2R \<phi>) \<longleftrightarrow> reflP P \<phi>"
unfolding reflP_def refl_on_def by force

lemma reflP_R2P[simp]: "reflP (S2P A) (R2P r) \<longleftrightarrow> refl_on A r"
unfolding reflP_def refl_on_def by auto

lemma sym_P2R[simp]: "sym (P2R \<phi>) \<longleftrightarrow> symP \<phi>"
unfolding symP_def sym_def by auto

lemma symP_R2P[simp]: "symP (R2P r) \<longleftrightarrow> sym r"
unfolding symP_def sym_def by auto

lemma trans_P2R[simp]: "trans (P2R \<phi>) \<longleftrightarrow> transP \<phi>"
unfolding transP_def trans_def by auto

lemma transP_R2P[simp]: "transP (R2P r) \<longleftrightarrow> trans r"
unfolding transP_def trans_def by auto

lemma equiv_P2R[simp]: "equiv (Collect P) (P2R \<phi>) \<longleftrightarrow> equivP P \<phi>"
unfolding equivP_def equiv_def by auto

lemma equivP_R2P[simp]: "equivP (S2P A) (R2P r) \<longleftrightarrow> equiv A r"
unfolding equivP_def equiv_def by auto

lemma in_P2R_Im_singl[simp]: "y \<in> P2R \<phi> `` {x} \<longleftrightarrow> \<phi> x y" by simp

definition proj :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set" where
"proj \<phi> x \<equiv> {y. \<phi> x y}"

lemma proj_P2R: "proj \<phi> x = P2R \<phi> `` {x}" unfolding proj_def by auto

lemma proj_P2R_raw: "proj \<phi> = (\<lambda> x. P2R \<phi> `` {x})"
apply(rule ext) unfolding proj_P2R ..

definition univ :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a set \<Rightarrow> 'b)"
where "univ f X == f (SOME x. x \<in> X)"

definition quotientP ::
"('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a set \<Rightarrow> bool)"  (infixl "'/'/'/" 90)
where "P /// \<phi> \<equiv> S2P ((Collect P) // (P2R \<phi>))"

lemma proj_preserves:
"P x \<Longrightarrow> (P /// \<phi>) (proj \<phi> x)"
unfolding proj_P2R quotientP_def
by (metis S2P_def mem_Collect_eq quotientI)

lemma proj_in_iff:
assumes "equivP P \<phi>"
shows "(P///\<phi>) (proj \<phi> x)  \<longleftrightarrow> P x"
using assms unfolding quotientP_def proj_def 
by (metis (mono_tags) Collect_mem_eq Equiv_Relation2.proj_def 
  Equiv_Relation2.proj_preserves S2P_Collect empty_Collect_eq equivP_def 
  equiv_P2R in_quotient_imp_non_empty quotientP_def reflP_def)

lemma proj_iff[simp]:
"\<lbrakk>equivP P \<phi>; P x; P y\<rbrakk> \<Longrightarrow> proj \<phi> x = proj \<phi> y \<longleftrightarrow> \<phi> x y"
unfolding proj_P2R
by (metis (full_types) equiv_P2R equiv_class_eq_iff equiv_class_self
          in_P2R_pair mem_Collect_eq proj_P2R proj_def)

lemma in_proj[simp]: "\<lbrakk>equivP P \<phi>; P x\<rbrakk> \<Longrightarrow> x \<in> proj \<phi> x"
unfolding proj_P2R equiv_def refl_on_def equiv_P2R[symmetric]
by auto

lemma proj_image[simp]: "(proj \<phi>) ` (Collect P) = Collect (P///\<phi>)"
unfolding proj_P2R_raw quotientP_def quotient_def by auto

lemma in_quotientP_imp_non_empty:
assumes "equivP P \<phi>" and "(P///\<phi>) X"
shows "X \<noteq> {}" 
by (metis R2P_P2R S2P_Collect S2P_def assms equivP_R2P 
in_quotient_imp_non_empty quotientP_def)

lemma in_quotientP_imp_in_rel:
"\<lbrakk>equivP P \<phi>; (P///\<phi>) X; x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> \<phi> x y"
unfolding equiv_P2R[symmetric] quotientP_def quotient_eq_iff
by (metis S2P_def in_P2R_pair quotient_eq_iff)

lemma in_quotientP_imp_closed:
"\<lbrakk>equivP P \<phi>; (P///\<phi>) X; x \<in> X; \<phi> x y\<rbrakk> \<Longrightarrow> y \<in> X"
using S2P_Collect S2P_def equivP_def proj_P2R_raw proj_def
        quotientE quotientP_def transP_def 
by metis 

lemma in_quotientP_imp_subset:
assumes "equivP P \<phi>" and "(P///\<phi>) X"
shows "X \<subseteq> Collect P"
by (metis (mono_tags, lifting) CollectI assms equivP_def in_quotientP_imp_in_rel reflP_def subsetI)

lemma equivP_pick_in:
assumes  "equivP P \<phi> " and "(P///\<phi>) X"
shows "pick X \<in> X"
by (metis assms in_quotientP_imp_non_empty pick_NE)

lemma equivP_pick_preserves:
assumes  "equivP P \<phi> " and "(P///\<phi>) X"
shows "P (pick X)"
by (metis assms equivP_pick_in in_quotientP_imp_subset mem_Collect_eq set_rev_mp)

lemma proj_pick:
assumes \<phi>: "equivP P \<phi>" and X: "(P///\<phi>) X"
shows "proj \<phi> (pick X) = X"
by (smt proj_def Equiv_Relation2.proj_iff Equiv_Relation2.proj_image X 
   \<phi> equivP_pick_in equivP_pick_preserves image_iff mem_Collect_eq)
 
lemma pick_proj:
assumes "equivP P \<phi>" and "P x"
shows "\<phi> (pick (proj \<phi> x)) x"
by (metis assms equivP_def in_proj mem_Collect_eq pick proj_def symP_def)

lemma equivP_pick_iff[simp]:
assumes \<phi>: "equivP P \<phi>" and X: "(P///\<phi>) X" and Y: "(P///\<phi>) Y"
shows "\<phi> (pick X) (pick Y) \<longleftrightarrow> X = Y"
by (metis Equiv_Relation2.proj_iff X Y \<phi> equivP_pick_preserves proj_pick)

lemma equivP_pick_inj_on:
assumes "equivP P \<phi>"
shows "inj_on pick (Collect (P///\<phi>))"
using assms unfolding inj_on_def
by (metis assms equivP_pick_iff mem_Collect_eq)

definition congruentP where
"congruentP \<phi> f \<equiv> \<forall> x y. \<phi> x y \<longrightarrow> f x = f y"

abbreviation RESPECTS_P (infixr "respectsP" 80) where
"f respectsP r == congruentP r f"

lemma congruent_P2R: "congruent (P2R \<phi>) f = congruentP \<phi> f"
unfolding congruent_def congruentP_def by auto
 
lemma univ_commute[simp]:
assumes "equivP P \<phi>" and "f respectsP \<phi>" and "P x"
shows "(univ f) (proj \<phi> x) = f x"
unfolding congruent_P2R[symmetric]
by (metis (full_types) assms pick_def congruentP_def pick_proj univ_def)

lemma univ_unique:
assumes "equivP P \<phi>" and "f respectsP \<phi>" and "\<And> x. P x \<Longrightarrow> G (proj \<phi> x) = f x"
shows "\<forall> X. (P///\<phi>) X \<longrightarrow> G X = univ f X"
by (metis assms equivP_pick_preserves proj_pick univ_commute)

lemma univ_preserves:
assumes "equivP P \<phi> " and "f respectsP \<phi>" and "\<And> x. P x \<Longrightarrow> f x \<in> B"
shows "\<forall> X. (P///\<phi>) X \<longrightarrow> univ f X \<in> B"
by (metis Equiv_Relation2.univ_commute assms  
          equivP_pick_preserves proj_pick) 




end
