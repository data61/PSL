(*  Author:     Tobias Nipkow, 2007  *)

theory QElin_opt
imports QElin
begin

subsubsection\<open>An optimization\<close>

text\<open>Atoms are simplified asap.\<close>

definition
"asimp a = (case a of
 Less r cs \<Rightarrow> (if \<forall>c\<in> set cs. c = 0
               then if r<0 then TrueF else FalseF
               else Atom a) |
 Eq r cs \<Rightarrow> (if \<forall>c\<in> set cs. c = 0
             then if r=0 then TrueF else FalseF else Atom a))"

lemma asimp_pretty:
"asimp (Less r cs) =
 (if \<forall>c\<in> set cs. c = 0
  then if r<0 then TrueF else FalseF
  else Atom(Less r cs))"
"asimp (Eq r cs) =
 (if \<forall>c\<in> set cs. c = 0
  then if r=0 then TrueF else FalseF
  else Atom(Eq r cs))"
by(auto simp:asimp_def)

definition qe_FMo\<^sub>1 :: "atom list \<Rightarrow> atom fm" where
"qe_FMo\<^sub>1 as = list_conj [asimp(combine p q). p\<leftarrow>lbounds as, q\<leftarrow>ubounds as]"

lemma I_asimp: "R.I (asimp a) xs = I\<^sub>R a xs"
by(simp add:asimp_def iprod0_if_coeffs0 split:atom.split)

lemma I_qe_FMo\<^sub>1: "R.I (qe_FMo\<^sub>1 as) xs = R.I (qe_FM\<^sub>1 as) xs"
by(simp add:qe_FM\<^sub>1_def qe_FMo\<^sub>1_def I_asimp)

definition "qe_FMo = R\<^sub>e.lift_dnfeq_qe qe_FMo\<^sub>1"

lemma qfree_qe_FMo\<^sub>1: "qfree (qe_FMo\<^sub>1 as)"
by(auto simp:qe_FM\<^sub>1_def qe_FMo\<^sub>1_def asimp_def intro!:qfree_list_conj
        split:atom.split)

corollary I_qe_FMo: "R.I (qe_FMo \<phi>) xs = R.I \<phi> xs"
unfolding qe_FMo_def
apply(rule R\<^sub>e.I_lift_dnfeq_qe)
 apply(rule qfree_qe_FMo\<^sub>1)
apply(rule allI)
apply(subst I_qe_FMo\<^sub>1)
apply(rule I_qe_FM\<^sub>1)
 prefer 2 apply blast
apply(clarify)
apply(drule_tac x=a in bspec) apply simp
apply(simp add: depends\<^sub>R_def split:atom.splits list.splits)
done

theorem qfree_qe_FMo: "qfree (qe_FMo f)"
by(simp add:qe_FMo_def R\<^sub>e.qfree_lift_dnfeq_qe qfree_qe_FMo\<^sub>1)

end
