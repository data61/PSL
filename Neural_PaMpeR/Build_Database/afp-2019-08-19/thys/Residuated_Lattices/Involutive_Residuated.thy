(* Title:      Involutive Residuated Structures
   Author:     Victor Gomes
   Maintainer: Victor Gomes <vborgesferreiragomes1 at sheffield.ac.uk>
*)

section \<open>Involutive Residuated Structures\<close>

theory Involutive_Residuated
  imports Residuated_Lattices
begin

class uminus' =
  fixes uminus' :: "'a \<Rightarrow> 'a" ("-' _" [81] 80)

text \<open>
  Involutive posets is a structure where the double negation property holds for the 
  negation operations, and a Galois connection for negations exists.
\<close>
class involutive_order = order + uminus + uminus' +
  assumes gn: "x \<le> -'y \<longleftrightarrow> y \<le> -x"
  and dn1[simp]: "-'(-x) = x"
  and dn2[simp]: "-(-'x) = x"
(* The involutive pair (-', -) is compatible with multiplication *)
class involutive_pogroupoid = order + times + involutive_order +
  assumes ipg1: "x\<cdot>y \<le> z \<longleftrightarrow> (-z)\<cdot>x \<le> -y"
  and ipg2: "x\<cdot>y \<le> z \<longleftrightarrow> y\<cdot>(-'z) \<le> -'x"
begin

lemma neg_antitone: "x \<le> y \<Longrightarrow> -y \<le> -x"
  by (metis local.dn1 local.gn)

lemma neg'_antitone: "x \<le> y \<Longrightarrow> -'y \<le> -'x"
  by (metis local.dn2 local.gn)
  
subclass pogroupoid
proof
  fix x y z assume assm: "x \<le> y"
  show "x \<cdot> z \<le> y \<cdot> z"
    by (metis assm local.ipg2 local.order_refl local.order_trans neg'_antitone)
  show "z \<cdot> x \<le> z \<cdot> y"
    by (metis assm local.dual_order.trans local.ipg1 local.order_refl neg_antitone)
qed

abbreviation inv_resl :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "inv_resl y x \<equiv> -(x\<cdot>(-'y))"
  
abbreviation inv_resr :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "inv_resr x y \<equiv> -'((-y)\<cdot>x)"

sublocale residuated_pogroupoid _ _ _ inv_resl inv_resr
proof
  fix x y z
  show "(x \<le> - (y \<cdot> -' z)) = (x \<cdot> y \<le> z)"
    by (metis local.gn local.ipg2)
  show "(x \<cdot> y \<le> z) = (y \<le> -' (- z \<cdot> x))"
    by (metis local.gn local.ipg1)
qed

end

class division_order = order + residual_l_op + residual_r_op +
  assumes div_galois: "x \<le> z \<leftarrow> y \<longleftrightarrow> y \<le> x \<rightarrow> z"
  
class involutive_division_order = division_order + involutive_order +
  assumes contraposition: "y \<rightarrow> -x = -'y \<leftarrow> x"
  
context involutive_pogroupoid begin
  
sublocale involutive_division_order _ _ inv_resl inv_resr 
proof
  fix x y z
  show "(x \<le> - (y \<cdot> -' z)) = (y \<le> -' (- z \<cdot> x))"
    by (metis local.gn local.ipg1 local.ipg2)
  show "-' (- (- x) \<cdot> y) = - (x \<cdot> -' (-' y))"
    by (metis local.dn1 local.dn2 local.eq_iff local.gn local.jipsen1l local.jipsen1r local.resl_galois local.resr_galois)
qed

lemma inv_resr_neg [simp]: "inv_resr (-x) (-y) = inv_resl x y"
  by (metis local.contraposition local.dn1)

lemma inv_resl_neg' [simp]: "inv_resl (-'x) (-'y) = inv_resr x y"
  by (metis local.contraposition local.dn2)
  
lemma neg'_mult_resl: "-'((-y)\<cdot>(-x)) = inv_resl x (-'y)"
  by (metis inv_resr_neg local.dn2)
  
lemma neg_mult_resr: "-((-'y)\<cdot>(-'x)) = inv_resr (-x) y"
  by (metis neg'_mult_resl)
  
lemma resr_de_morgan1: "-'(inv_resr (-y) (-x)) = -'(inv_resl y x)"
  by (metis local.dn1 neg_mult_resr)

lemma resr_de_morgan2: "-(inv_resl (-'x) (-'y)) = -(inv_resr x y)"
  by (metis inv_resl_neg')
  
end

text \<open>
  We prove that an involutive division poset is equivalent to an involutive po-groupoid
  by a lemma to avoid cyclic definitions
\<close>
lemma (in involutive_division_order) inv_pogroupoid: 
  "class.involutive_pogroupoid (\<lambda>x y. -(y \<rightarrow> -'x)) uminus uminus' (\<le>) (<)"
proof
  fix x y z
  have "(- (y \<rightarrow> -' x) \<le> z) = (-z \<le> -y \<leftarrow> x)"
    by (metis local.contraposition local.dn1 local.dn2 local.gn local.div_galois)
  thus "(- (y \<rightarrow> -' x) \<le> z) = (- (x \<rightarrow> -' (- z)) \<le> - y)"
    by (metis local.contraposition local.div_galois local.dn1 local.dn2 local.gn)
  moreover have "(- (x \<rightarrow> -' (- z)) \<le> - y) = (- (-' z \<rightarrow> -' y) \<le> -' x)"
    apply (auto, metis local.contraposition local.div_galois local.dn1 local.dn2 local.gn)
    by (metis local.contraposition local.div_galois local.dn1 local.dn2 local.gn)
  ultimately show "(- (y \<rightarrow> -' x) \<le> z) = (- (-' z \<rightarrow> -' y) \<le> -' x)" 
    by metis
qed

context involutive_pogroupoid begin

definition negation_constant :: "'a \<Rightarrow> bool" where
  "negation_constant a \<equiv> \<forall>x. -'x = inv_resr x a \<and> -x = inv_resl a x"   
  
definition division_unit :: "'a \<Rightarrow> bool" where
  "division_unit a \<equiv> \<forall>x. x = inv_resr a x \<and> x = inv_resl x a"
  
lemma neg_iff_div_unit: "(\<exists>a. negation_constant a) \<longleftrightarrow> (\<exists>b. division_unit b)"
  unfolding negation_constant_def division_unit_def
  apply safe
  apply (rule_tac x="-a" in exI, auto)
  apply (metis local.dn1 local.dn2)
  apply (metis local.dn2)
  apply (rule_tac x="-b" in exI, auto)
  apply (metis local.contraposition)
  apply (metis local.dn2)
done

end

end
