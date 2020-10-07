section \<open>Stutter Invariance of next-free LTL Formula\<close>

theory LTL_Stutter
  imports LTL.LTL Stuttering_Equivalence.PLTL
begin

text \<open>This theory builds on the AFP-entry by Stephan Merz\<close>

primrec ltlc_next_free :: "'a ltlc \<Rightarrow> bool"
  where
    "ltlc_next_free true\<^sub>c = True"
  | "ltlc_next_free false\<^sub>c = True"
  | "ltlc_next_free (prop\<^sub>c(q)) = True"
  | "ltlc_next_free (not\<^sub>c \<phi>) = ltlc_next_free \<phi>"
  | "ltlc_next_free (\<phi> and\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (\<phi> or\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (\<phi> implies\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (X\<^sub>c \<phi>) = False"
  | "ltlc_next_free (F\<^sub>c \<phi>) = ltlc_next_free \<phi>"
  | "ltlc_next_free (G\<^sub>c \<phi>) = ltlc_next_free \<phi>"
  | "ltlc_next_free (\<phi> U\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (\<phi> R\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (\<phi> W\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"
  | "ltlc_next_free (\<phi> M\<^sub>c \<psi>) = (ltlc_next_free \<phi> \<and> ltlc_next_free \<psi>)"

text \<open>Conversion between the two LTL formalizations\<close>

lemma PLTL_next_free_cnv[simp]: "PLTL.next_free (ltlc_to_pltl \<phi>) \<longleftrightarrow> ltlc_next_free \<phi>"
  by (induction \<phi>) auto

\<comment> \<open>A next free formula cannot distinguish between stutter-equivalent runs.\<close>
theorem next_free_stutter_invariant: 
  assumes next_free: "ltlc_next_free \<phi>"
  assumes eq: "r \<approx> r'"
  shows "r \<Turnstile>\<^sub>c \<phi> \<longleftrightarrow> r' \<Turnstile>\<^sub>c \<phi>"
proof -
  {
    fix r r'
    assume eq: "r \<approx> r'" and holds: "r \<Turnstile>\<^sub>c \<phi>"
    then have "r \<Turnstile>\<^sub>p (ltlc_to_pltl \<phi>)"by simp
    
    from next_free_stutter_invariant[of "ltlc_to_pltl \<phi>"] next_free 
    have "PLTL.stutter_invariant (ltlc_to_pltl \<phi>)" by simp
    from stutter_invariantD[OF this eq] holds have "r' \<Turnstile>\<^sub>c \<phi>" by simp
  } note aux=this
  
  from aux[of r r'] aux[of r' r] eq stutter_equiv_sym[OF eq] show ?thesis
    by blast
qed

end

