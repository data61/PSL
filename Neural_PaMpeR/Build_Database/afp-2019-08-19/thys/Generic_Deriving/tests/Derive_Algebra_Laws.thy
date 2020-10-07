subsection "Algebraic Classes"

theory Derive_Algebra_Laws
  imports Main "../Derive" Derive_Datatypes
begin

datatype simple_int = A int | B int int | C 

class semigroup = 
  fixes mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)" 

class monoidl = semigroup +
  fixes neutral :: 'a ("\<one>")
  assumes neutl : "\<one> \<otimes> x = x"   
  
class group = monoidl +
  fixes inverse :: "'a \<Rightarrow> 'a"
  assumes invl: "(inverse x) \<otimes> x = \<one>" 

definition semigroup_law :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
"semigroup_law MULT = (\<forall> x y z. MULT (MULT x y) z = MULT x (MULT y z))"
definition monoidl_law :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
"monoidl_law NEUTRAL MULT = ((\<forall> x. MULT NEUTRAL x = x) \<and> semigroup_law MULT)"
definition group_law :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
"group_law INVERSE NEUTRAL MULT = ((\<forall> x. MULT (INVERSE x) x = NEUTRAL) \<and> monoidl_law NEUTRAL MULT)"

lemma transfer_semigroup:
  assumes "Derive.iso f g"
  shows "semigroup_law MULT \<Longrightarrow> semigroup_law (\<lambda>x y. g (MULT (f x) (f y)))"
  unfolding semigroup_law_def
  using assms unfolding Derive.iso_def by simp

lemma transfer_monoidl:
  assumes "Derive.iso f g"
  shows "monoidl_law NEUTRAL MULT \<Longrightarrow> monoidl_law (g NEUTRAL) (\<lambda>x y. g (MULT (f x) (f y)))"
  unfolding monoidl_law_def semigroup_law_def 
  using assms unfolding Derive.iso_def by simp

lemma transfer_group:
  assumes "Derive.iso f g"
  shows "group_law INVERSE NEUTRAL MULT \<Longrightarrow> group_law (\<lambda> x. g (INVERSE (f x))) (g NEUTRAL) (\<lambda>x y. g (MULT (f x) (f y)))"
  unfolding group_law_def monoidl_law_def semigroup_law_def
  using assms unfolding Derive.iso_def by simp

lemma semigroup_law_semigroup: "semigroup_law mult"
  unfolding semigroup_law_def
  using semigroup_class.axioms unfolding class.semigroup_def .

lemma monoidl_law_monoidl: "monoidl_law neutral mult"
  unfolding monoidl_law_def
  using monoidl_class.axioms semigroup_law_semigroup 
  unfolding class.monoidl_axioms_def by simp

lemma group_law_group: "group_law inverse neutral mult"
  unfolding group_law_def
  using group_class.axioms monoidl_law_monoidl 
  unfolding class.group_axioms_def by simp

derive_generic_setup semigroup
  unfolding semigroup_class_law_def
  Derive.iso_def
  by simp

derive_generic_setup monoidl
  unfolding monoidl_class_law_def semigroup_class_law_def Derive.iso_def 
  by simp

derive_generic_setup group
  unfolding group_class_law_def monoidl_class_law_def semigroup_class_law_def Derive.iso_def 
  by simp

(* Manual instances for int, unit, prod, and sum *)    
instantiation int and unit:: semigroup
begin  
  definition mult_int_def : "mult (x::int) y = x + y"
  definition mult_unit_def: "mult (x::unit) y = x"
instance proof
  fix x y z :: int
  show "x \<otimes> y \<otimes> z = x \<otimes> (y \<otimes> z)"
    unfolding mult_int_def by simp
next
  fix x y z :: unit
  show "x \<otimes> y \<otimes> z = x \<otimes> (y \<otimes> z)"
    unfolding mult_unit_def by simp
qed
end 
instantiation int and unit:: monoidl
begin  
  definition neutral_int_def : "neutral = (0::int)"
  definition neutral_unit_def: "neutral = ()"
instance proof
  fix x :: int
  show "\<one> \<otimes> x = x" unfolding neutral_int_def mult_int_def by simp
next
  fix x :: unit
  show "\<one> \<otimes> x = x" unfolding neutral_unit_def mult_unit_def by simp
qed
end   
  
instantiation int and unit:: group
begin  
  definition inverse_int_def : "inverse (i::int) = \<one> - i"
  definition inverse_unit_def: "inverse u = ()"
instance proof
  fix x :: int
  show "inverse x \<otimes> x = \<one>" unfolding inverse_int_def mult_int_def by simp
next
  fix x :: unit
  show "inverse x \<otimes> x = \<one>" unfolding inverse_unit_def mult_unit_def by simp
qed
end   

instantiation prod and sum :: (semigroup, semigroup) semigroup
begin
  definition mult_prod_def: "x \<otimes> y = (fst x \<otimes> fst y, snd x \<otimes> snd y)"
  definition mult_sum_def: "x \<otimes> y = (case x of Inl a \<Rightarrow> (case y of Inl b \<Rightarrow> Inl (a \<otimes> b) | Inr b \<Rightarrow> Inr b)
                                             | Inr a \<Rightarrow> (case y of Inl b \<Rightarrow> Inr a | Inr b \<Rightarrow> Inr (a \<otimes> b)))"
instance proof
  fix x y z :: "('a::semigroup) \<times> ('b::semigroup)"
  show "x \<otimes> y \<otimes> z = x \<otimes> (y \<otimes> z)" unfolding mult_prod_def by (simp add: assoc)
next
  fix x y z :: "('a::semigroup) + ('b::semigroup)"
  show "x \<otimes> y \<otimes> z = x \<otimes> (y \<otimes> z)" unfolding mult_sum_def
    by (simp add: assoc sum.case_eq_if) 
qed
end
  
instantiation prod and sum :: (monoidl, monoidl) monoidl
begin
  definition neutral_prod_def: "neutral = (neutral,neutral)"
  definition neutral_sum_def: "neutral = Inl neutral"
instance proof
  fix x :: "('a::monoidl) \<times> ('b::monoidl)"
  show "\<one> \<otimes> x = x" unfolding neutral_prod_def mult_prod_def by (simp add: neutl)
next
  fix x :: "('a::monoidl) + ('b::monoidl)"
  show "\<one> \<otimes> x = x" unfolding neutral_sum_def mult_sum_def
    by (simp add: neutl sum.case_eq_if sum.exhaust_sel) 
qed
end 
  
instantiation prod :: (group, group) group
begin
  definition inverse_prod_def: "inverse p = (inverse (fst p), inverse (snd p))"
instance proof
  fix x :: "('a::group) \<times> ('b::group)"
  show "inverse x \<otimes> x = \<one>" unfolding inverse_prod_def mult_prod_def neutral_prod_def
    by (simp add: invl)
qed
end


derive_generic semigroup simple_int .
derive_generic monoidl simple_int .

derive_generic semigroup either .
derive_generic monoidl either .

lemma "(B \<one> 6) \<otimes> (B 4 5) = B 4 11" by eval
lemma "(A 2) \<otimes> (A 3) = A 5" by eval
lemma "(B \<one> 6) \<otimes> \<one> = B 0 6" by eval

lemma "(L 3) \<otimes> ((L 4)::(int,int) either) = L 7" by eval
lemma "(R (2::int)) \<otimes> (L (3::int)) = R 2" by eval

derive_generic semigroup list
proof goal_cases
  case (1 x y z)
  then show ?case
  proof (induction x arbitrary: y z)
    case (In x')
    then show ?case
      apply(cases x')
      apply (cases y; cases z; hypsubst_thin)
       apply (simp add: Derive_Algebra_Laws.mult_mulistF.simps sum.case_eq_if mult_unit_def)
      apply(cases y; cases z; hypsubst_thin)
      unfolding sum_set_defs prod_set_defs
      apply (simp add: Derive_Algebra_Laws.mult_mulistF.simps mult_unit_def)
      by (simp add: sum.case_eq_if assoc)
  qed
qed    

derive_generic semigroup tree
proof goal_cases
  case (1 x y z)
  then show ?case
  proof (induction x arbitrary: y z)
    case (In x')
    then show ?case
      apply(cases x')
      apply (cases y; cases z; hypsubst_thin)
       apply (simp add: Derive_Algebra_Laws.mult_mutreeF.simps sum.case_eq_if mult_unit_def)
      apply(cases y; cases z; hypsubst_thin)
      unfolding sum_set_defs prod_set_defs
      apply (simp add: Derive_Algebra_Laws.mult_mutreeF.simps mult_unit_def)
      by (simp add: semigroup_class.assoc sum.case_eq_if) 
  qed
qed

derive_generic monoidl list
proof goal_cases
  case (1 x)
  then show ?case
  proof (induction x)
    case (In x')
    then show ?case
      apply(cases x')
      by (auto simp add: Derive_Algebra_Laws.neutral_mulistF_def sum.case_eq_if neutral_unit_def)
  qed
qed

derive_generic monoidl tree
proof goal_cases
  case (1 x)
  then show ?case
  proof (induction x)
    case (In x')
    then show ?case
      apply(cases x')
      by (auto simp add: Derive_Algebra_Laws.neutral_mutreeF_def sum.case_eq_if neutral_unit_def)
  qed
qed

lemma "[1,2,3,4::int] \<otimes> [1,2,3] = [2,4,6,4]" by eval
lemma "(Node (3::int) Leaf Leaf) \<otimes> (Node (1::int) Leaf Leaf) = (Node 4 Leaf Leaf)" by eval

end