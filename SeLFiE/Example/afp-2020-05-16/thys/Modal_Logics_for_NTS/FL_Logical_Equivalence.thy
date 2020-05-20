theory FL_Logical_Equivalence
imports
  FL_Validity
begin

section \<open>(Strong) Logical Equivalence\<close>

text \<open>The definition of formulas is parametric in the index type, but from now on we want to work
with a fixed (sufficiently large) index type.\<close>

locale indexed_effect_nominal_ts = effect_nominal_ts satisfies transition effect_apply
  for satisfies :: "'state::fs \<Rightarrow> 'pred::fs \<Rightarrow> bool" (infix "\<turnstile>" 70)
  and transition :: "'state \<Rightarrow> ('act::bn,'state) residual \<Rightarrow> bool" (infix "\<rightarrow>" 70)
  and effect_apply :: "'effect::fs \<Rightarrow> 'state \<Rightarrow> 'state" ("\<langle>_\<rangle>_" [0,101] 100) +
  assumes card_idx_perm: "|UNIV::perm set| <o |UNIV::'idx set|"
      and card_idx_state: "|UNIV::'state set| <o |UNIV::'idx set|"
begin

  definition FL_logically_equivalent :: "'effect first \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
    "FL_logically_equivalent F P Q \<equiv>
       \<forall>x::('idx,'pred,'act,'effect) formula. x \<in> \<A>[F] \<longrightarrow> (P \<Turnstile> x \<longleftrightarrow> Q \<Turnstile> x)"

  text \<open>We could (but didn't need to) prove that this defines an equivariant equivalence relation.\<close>

end

end
