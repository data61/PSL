section \<open> Expression Type Class Instantiations \<close>

theory utp_expr_insts
  imports utp_expr
begin

text \<open> It should be noted that instantiating the unary minus class, @{class uminus}, will also 
  provide negation UTP predicates later. \<close>

instantiation uexpr :: (uminus, type) uminus
begin
  definition uminus_uexpr_def [uexpr_defs]: "- u = uop uminus u"
instance ..
end

instantiation uexpr :: (minus, type) minus
begin
  definition minus_uexpr_def [uexpr_defs]: "u - v = bop (-) u v"
instance ..
end

instantiation uexpr :: (times, type) times
begin
  definition times_uexpr_def [uexpr_defs]: "u * v = bop times u v"
instance ..
end

instance uexpr :: (Rings.dvd, type) Rings.dvd ..

instantiation uexpr :: (divide, type) divide
begin
  definition divide_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr" where
  [uexpr_defs]: "divide_uexpr u v = bop divide u v"
instance ..
end

instantiation uexpr :: (inverse, type) inverse
begin
  definition inverse_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr"
  where [uexpr_defs]: "inverse_uexpr u = uop inverse u"
instance ..
end

instantiation uexpr :: (modulo, type) modulo
begin
  definition mod_uexpr_def [uexpr_defs]: "u mod v = bop (mod) u v"
instance ..
end

instantiation uexpr :: (sgn, type) sgn
begin
  definition sgn_uexpr_def [uexpr_defs]: "sgn u = uop sgn u"
instance ..
end

instantiation uexpr :: (abs, type) abs
begin
  definition abs_uexpr_def [uexpr_defs]: "abs u = uop abs u"
instance ..
end

text \<open> Once we've set up all the core constructs for arithmetic, we can also instantiate the 
  type classes for various algebras, including groups and rings. The proofs are done by 
  definitional expansion, the \emph{transfer} tactic, and then finally the theorems of the underlying
  HOL operators. This is mainly routine, so we don't comment further. \<close>
  
instance uexpr :: (semigroup_mult, type) semigroup_mult
  by (intro_classes) (simp add: times_uexpr_def one_uexpr_def, transfer, simp add: mult.assoc)+

instance uexpr :: (monoid_mult, type) monoid_mult
  by (intro_classes) (simp add: times_uexpr_def one_uexpr_def, transfer, simp)+

instance uexpr :: (monoid_add, type) monoid_add
  by (intro_classes) (simp add: plus_uexpr_def zero_uexpr_def, transfer, simp)+

instance uexpr :: (ab_semigroup_add, type) ab_semigroup_add
  by (intro_classes) (simp add: plus_uexpr_def, transfer, simp add: add.commute)+

instance uexpr :: (cancel_semigroup_add, type) cancel_semigroup_add
  by (intro_classes) (simp add: plus_uexpr_def, transfer, simp add: fun_eq_iff)+

instance uexpr :: (cancel_ab_semigroup_add, type) cancel_ab_semigroup_add
  by (intro_classes, (simp add: plus_uexpr_def minus_uexpr_def, transfer, simp add: fun_eq_iff add.commute cancel_ab_semigroup_add_class.diff_diff_add)+)

instance uexpr :: (group_add, type) group_add
  by (intro_classes)
     (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def zero_uexpr_def, transfer, simp)+

instance uexpr :: (ab_group_add, type) ab_group_add
  by (intro_classes)
     (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def zero_uexpr_def, transfer, simp)+

instance uexpr :: (semiring, type) semiring
  by (intro_classes) (simp add: plus_uexpr_def times_uexpr_def, transfer, simp add: fun_eq_iff add.commute semiring_class.distrib_right semiring_class.distrib_left)+

instance uexpr :: (ring_1, type) ring_1
  by (intro_classes) (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def times_uexpr_def zero_uexpr_def one_uexpr_def, transfer, simp add: fun_eq_iff)+

text \<open> We also lift the properties from certain ordered groups. \<close>
  
instance uexpr :: (ordered_ab_group_add, type) ordered_ab_group_add
  by (intro_classes) (simp add: plus_uexpr_def, transfer, simp)

instance uexpr :: (ordered_ab_group_add_abs, type) ordered_ab_group_add_abs
  apply (intro_classes)
      apply (simp add: abs_uexpr_def zero_uexpr_def plus_uexpr_def uminus_uexpr_def, transfer, simp add: abs_ge_self abs_le_iff abs_triangle_ineq)+
  apply (metis ab_group_add_class.ab_diff_conv_add_uminus abs_ge_minus_self abs_ge_self add_mono_thms_linordered_semiring(1))
  done

text \<open> The next theorem lifts powers. \<close>

lemma power_rep_eq [ueval]: "\<lbrakk>P ^ n\<rbrakk>\<^sub>e = (\<lambda> b. \<lbrakk>P\<rbrakk>\<^sub>e b ^ n)"
  by (induct n, simp_all add: lit.rep_eq one_uexpr_def bop.rep_eq times_uexpr_def)

lemma of_nat_uexpr_rep_eq [ueval]: "\<lbrakk>of_nat x\<rbrakk>\<^sub>e b = of_nat x"
  by (induct x, simp_all add: uexpr_defs ueval)

lemma lit_uminus [lit_simps]: "\<guillemotleft>- x\<guillemotright> = - \<guillemotleft>x\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_minus [lit_simps]: "\<guillemotleft>x - y\<guillemotright> = \<guillemotleft>x\<guillemotright> - \<guillemotleft>y\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_times [lit_simps]: "\<guillemotleft>x * y\<guillemotright> = \<guillemotleft>x\<guillemotright> * \<guillemotleft>y\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_divide [lit_simps]: "\<guillemotleft>x / y\<guillemotright> = \<guillemotleft>x\<guillemotright> / \<guillemotleft>y\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_div [lit_simps]: "\<guillemotleft>x div y\<guillemotright> = \<guillemotleft>x\<guillemotright> div \<guillemotleft>y\<guillemotright>" by (simp add: uexpr_defs, transfer, simp)
lemma lit_power [lit_simps]: "\<guillemotleft>x ^ n\<guillemotright> = \<guillemotleft>x\<guillemotright> ^ n" by (simp add: lit.rep_eq power_rep_eq uexpr_eq_iff)

subsection \<open> Expression construction from HOL terms \<close>

text \<open> Sometimes it is convenient to cast HOL terms to UTP expressions, and these simplifications
  automate this process. \<close>

named_theorems mkuexpr

lemma mkuexpr_lens_get [mkuexpr]: "mk\<^sub>e get\<^bsub>x\<^esub> = &x"
  by (transfer, simp add: pr_var_def)

lemma mkuexpr_zero [mkuexpr]: "mk\<^sub>e (\<lambda> s. 0) = 0"
  by (simp add: zero_uexpr_def, transfer, simp)

lemma mkuexpr_one [mkuexpr]: "mk\<^sub>e (\<lambda> s. 1) = 1"
  by (simp add: one_uexpr_def, transfer, simp)

lemma mkuexpr_numeral [mkuexpr]: "mk\<^sub>e (\<lambda> s. numeral n) = numeral n"
  using lit_numeral_2 by blast

lemma mkuexpr_lit [mkuexpr]: "mk\<^sub>e (\<lambda> s. k) = \<guillemotleft>k\<guillemotright>"
  by (transfer, simp)

lemma mkuexpr_pair [mkuexpr]: "mk\<^sub>e (\<lambda>s. (f s, g s)) = (mk\<^sub>e f, mk\<^sub>e g)\<^sub>u"
  by (transfer, simp)

lemma mkuexpr_plus [mkuexpr]: "mk\<^sub>e (\<lambda> s. f s + g s) = mk\<^sub>e f + mk\<^sub>e g"
  by (simp add: plus_uexpr_def, transfer, simp)

lemma mkuexpr_uminus [mkuexpr]: "mk\<^sub>e (\<lambda> s. - f s) = - mk\<^sub>e f"
  by (simp add: uminus_uexpr_def, transfer, simp)

lemma mkuexpr_minus [mkuexpr]: "mk\<^sub>e (\<lambda> s. f s - g s) = mk\<^sub>e f - mk\<^sub>e g"
  by (simp add: minus_uexpr_def, transfer, simp)

lemma mkuexpr_times [mkuexpr]: "mk\<^sub>e (\<lambda> s. f s * g s) = mk\<^sub>e f * mk\<^sub>e g"
  by (simp add: times_uexpr_def, transfer, simp)

lemma mkuexpr_divide [mkuexpr]: "mk\<^sub>e (\<lambda> s. f s / g s) = mk\<^sub>e f / mk\<^sub>e g"
  by (simp add: divide_uexpr_def, transfer, simp)

end