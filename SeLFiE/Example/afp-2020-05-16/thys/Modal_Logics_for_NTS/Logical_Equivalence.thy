theory Logical_Equivalence
imports
  Validity
begin

section \<open>(Strong) Logical Equivalence\<close>

text \<open>The definition of formulas is parametric in the index type, but from now on we want to work
with a fixed (sufficiently large) index type.\<close>

locale indexed_nominal_ts = nominal_ts satisfies transition
  for satisfies :: "'state::fs \<Rightarrow> 'pred::fs \<Rightarrow> bool" (infix "\<turnstile>" 70)
  and transition :: "'state \<Rightarrow> ('act::bn,'state) residual \<Rightarrow> bool" (infix "\<rightarrow>" 70) +
  assumes card_idx_perm: "|UNIV::perm set| <o |UNIV::'idx set|"
      and card_idx_state: "|UNIV::'state set| <o |UNIV::'idx set|"
begin

  definition logically_equivalent :: "'state \<Rightarrow> 'state \<Rightarrow> bool" where
    "logically_equivalent P Q \<equiv> (\<forall>x::('idx,'pred,'act) formula. P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x)"

  notation logically_equivalent (infix "=\<cdot>" 50)

  lemma logically_equivalent_eqvt:
    assumes "P =\<cdot> Q" shows "p \<bullet> P =\<cdot> p \<bullet> Q"
  using assms unfolding logically_equivalent_def
  by (metis (mono_tags) permute_minus_cancel(1) valid_eqvt)

end

end
