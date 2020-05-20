section "Classes with Laws"

subsection "Equality"

theory Derive_Eq_Laws
  imports Main "../Derive" Derive_Datatypes
begin

class eq =
  fixes eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes refl: "eq x x" and
          sym: "eq x y \<Longrightarrow> eq y x" and
          trans: "eq x y \<Longrightarrow> eq y z \<Longrightarrow> eq x z"

derive_generic_setup eq
  unfolding eq_class_law_def
  by blast

lemma eq_law_eq: "eq_class_law eq"
  unfolding eq_class_law_def
  using eq_class.axioms unfolding class.eq_def .

(* Manual instances for nat, unit, prod, and sum *)
instantiation nat and unit :: eq
begin
  definition eq_nat_def : "eq (x::nat) y \<longleftrightarrow> x = y"
  definition eq_unit_def: "eq (x::unit) y \<longleftrightarrow> True"
instance proof
  fix x y z :: nat
  show "eq x x" unfolding eq_nat_def by simp
  show "eq x y \<Longrightarrow> eq y x" unfolding eq_nat_def by simp
  show "eq x y \<Longrightarrow> eq y z \<Longrightarrow> eq x z" unfolding eq_nat_def by simp
next
  fix x y z :: unit
  show "eq x x" unfolding eq_unit_def by simp
  show "eq x y \<Longrightarrow> eq y x" unfolding eq_unit_def by simp
  show "eq x y \<Longrightarrow> eq y z \<Longrightarrow> eq x z" unfolding eq_unit_def by simp
qed
end

instantiation prod and sum :: (eq, eq) eq
begin
  definition eq_prod_def: "eq x y \<longleftrightarrow> (eq (fst x) (fst y)) \<and> (eq (snd x) (snd y))"
  definition eq_sum_def: "eq x y = (case x of Inl a \<Rightarrow> (case y of Inl b \<Rightarrow> eq a b | Inr b \<Rightarrow> False)
                                            | Inr a \<Rightarrow> (case y of Inl b \<Rightarrow> False | Inr b \<Rightarrow> eq a b))"
instance proof
  fix x y z :: "('a::eq) \<times> ('b::eq)"
  show "eq x x" unfolding eq_prod_def by (simp add: eq_class.refl)
  show "eq x y \<Longrightarrow> eq y x" unfolding eq_prod_def by (simp add: eq_class.sym)
  show "eq x y \<Longrightarrow> eq y z \<Longrightarrow> eq x z" unfolding eq_prod_def by (meson eq_class.trans)
next
  fix x y z :: "('a::eq) + ('b::eq)"
  show "eq x x" unfolding eq_sum_def by (simp add: sum.case_eq_if eq_class.refl)
  show "eq x y \<Longrightarrow> eq y x" unfolding eq_sum_def by (metis eq_class.sym sum.case_eq_if)
  show "eq x y \<Longrightarrow> eq y z \<Longrightarrow> eq x z" 
    unfolding eq_sum_def 
    apply (simp only: sum.case_eq_if)
    apply (cases "isl x"; cases "isl y"; cases "isl z")
    by (auto simp add: eq_class.trans)
qed
end

(* nonrecursive test *)
derive_generic eq simple .

(* some tests *)
lemma "eq (A 4) (A 4)" by eval
lemma "eq (A 6) (A 4) \<longleftrightarrow> False" by eval
lemma "eq C C" by eval
lemma "eq (B 4 5) (B 4 5)" by eval
lemma "eq (B 4 4) (A 3) \<longleftrightarrow> False" by eval
lemma "eq C (A 4) \<longleftrightarrow> False" by eval

(* type with parameter *)

derive_generic eq either .

lemma "eq (L (3::nat)) (R 3) \<longleftrightarrow> False" by code_simp
lemma "eq (L (3::nat)) (L 3)" by code_simp
lemma "eq (L (3::nat)) (L 4) \<longleftrightarrow> False" by code_simp

(* recursive types *)
derive_generic eq list
proof goal_cases
  case (1 x)
  then show ?case
  proof (induction x)
    case (In y)
    then show ?case
      apply(cases y)
      by (auto simp add: Derive_Eq_Laws.eq_mulistF.simps eq_unit_def eq_class.refl)
  qed
next
  case (2 x y)
  then show ?case
  proof (induction y arbitrary: x)
    case (In y)
    then show ?case
      apply(cases x; cases y; hypsubst_thin)
       apply (simp add: Derive_Eq_Laws.eq_mulistF.simps sum.case_eq_if eq_unit_def)
       apply(metis old.sum.simps(5))
      unfolding sum_set_defs prod_set_defs
      apply (simp add: Derive_Eq_Laws.eq_mulistF.simps sum.case_eq_if)
      using eq_class.sym by fastforce
  qed
next      
  case (3 x y z)
  then show ?case
  proof (induction x arbitrary: y z)
    case (In x')
    then show ?case
      apply(cases x')
      apply (cases y; cases z; hypsubst_thin)
       apply (simp add: Derive_Eq_Laws.eq_mulistF.simps sum.case_eq_if eq_unit_def)
       apply (metis sum.case_eq_if)
      apply(cases y; cases z; hypsubst_thin)
      unfolding sum_set_defs prod_set_defs
      apply (simp add: Derive_Eq_Laws.eq_mulistF.simps eq_unit_def snds.intros)
      apply (simp only: sum.case_eq_if)
      by (meson eq_class.trans)
  qed
qed

lemma "eq ([]::(nat list)) []" by eval
lemma "eq ([1,2,3]:: (nat list)) [1,2,3]" by eval
lemma "eq [(1::nat)] [1,2] \<longleftrightarrow> False" by eval

derive_generic eq tree 
proof goal_cases
  case (1 x)
  then show ?case
  proof (induction x)
    case (In y)
    then show ?case
      apply(cases y)
      by (auto simp add: Derive_Eq_Laws.eq_mutreeF.simps eq_unit_def eq_class.refl)
  qed
next
  case (2 x y)
  then show ?case
  proof (induction y arbitrary: x)
    case (In y)
    then show ?case
      apply(cases x; cases y; hypsubst_thin)
       apply (simp add: Derive_Eq_Laws.eq_mutreeF.simps sum.case_eq_if eq_unit_def)
       apply(metis old.sum.simps(5))
      unfolding sum_set_defs prod_set_defs
      apply (simp add: Derive_Eq_Laws.eq_mutreeF.simps sum.case_eq_if)
      using eq_class.sym by fastforce
  qed
next      
  case (3 x y z)
  then show ?case
  proof (induction x arbitrary: y z)
    case (In x')
    then show ?case
      apply(cases x')
      apply (cases y; cases z; hypsubst_thin)
       apply (simp add: Derive_Eq_Laws.eq_mutreeF.simps sum.case_eq_if eq_unit_def)
       apply (metis sum.case_eq_if)
      apply(cases y; cases z; hypsubst_thin)
      unfolding sum_set_defs prod_set_defs
      apply (simp add: Derive_Eq_Laws.eq_mutreeF.simps eq_unit_def snds.intros)
      apply (simp only: sum.case_eq_if)
      by (meson eq_class.trans)
  qed
qed

lemma "eq Leaf Leaf" by code_simp
lemma "eq (Node (1::nat) Leaf Leaf) Leaf \<longleftrightarrow> False" by eval
lemma "eq (Node (1::nat) Leaf Leaf) (Node (1::nat) Leaf Leaf)" by eval
lemma "eq (Node (1::nat) (Node 2 Leaf Leaf) (Node 3 Leaf Leaf)) (Node (1::nat) (Node 2 Leaf Leaf) (Node 4 Leaf Leaf)) 
    \<longleftrightarrow> False" by eval
end