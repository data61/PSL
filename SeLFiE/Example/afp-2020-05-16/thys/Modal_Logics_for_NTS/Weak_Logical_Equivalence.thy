theory Weak_Logical_Equivalence
imports
  Weak_Formula
  Weak_Validity
begin

section \<open>Weak Logical Equivalence\<close>

context indexed_weak_nominal_ts
begin

  text \<open>Two states are weakly logically equivalent if they validate the same weak formulas.\<close>

  definition weakly_logically_equivalent :: "'state \<Rightarrow> 'state \<Rightarrow> bool" where
    "weakly_logically_equivalent P Q \<equiv> (\<forall>x::('idx,'pred,'act) formula. weak_formula x \<longrightarrow> P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x)"

  notation weakly_logically_equivalent (infix "\<equiv>\<cdot>" 50)

  lemma weakly_logically_equivalent_eqvt:
    assumes "P \<equiv>\<cdot> Q" shows "p \<bullet> P \<equiv>\<cdot> p \<bullet> Q"
  unfolding weakly_logically_equivalent_def proof (clarify)
    fix x :: "('idx,'pred,'act) formula"
    assume "weak_formula x"
    then have "weak_formula (-p \<bullet> x)"
      by simp
    then show "p \<bullet> P \<Turnstile> x \<longleftrightarrow> p \<bullet> Q \<Turnstile> x"
      using assms by (metis (no_types, lifting) weakly_logically_equivalent_def permute_minus_cancel(2) valid_eqvt)
  qed

end

end
