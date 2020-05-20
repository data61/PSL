section \<open>Partial Function Package Setup\<close>
theory Refine_Pfun
imports Refine_Basic Refine_Det
begin

text \<open>
  In this theory, we set up the partial function package to be used 
  with our refinement framework.
\<close>

subsection \<open>Nondeterministic Result Monad\<close>

interpretation nrec:
  partial_function_definitions "(\<le>)" "Sup::'a nres set \<Rightarrow> 'a nres"
  by unfold_locales (auto simp add: Sup_upper Sup_least)

lemma nrec_admissible: "nrec.admissible (\<lambda>(f::'a \<Rightarrow> 'b nres).
  (\<forall>x0. f x0 \<le> SPEC (P x0)))"
  apply (rule ccpo.admissibleI)
  apply (unfold fun_lub_def)
  apply (intro allI impI)
  apply (rule Sup_least)
  apply auto
  done

(*thm fixp_induct_option

lemma fixp_induct_nrec:
  fixes F :: "'c \<Rightarrow> 'c" and
    U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a nres" and
    C :: "('b \<Rightarrow> 'a nres) \<Rightarrow> 'c" and
    P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono: "\<And>x. nrec.mono_body (\<lambda>f. U (F (C f)) x)"                       
  assumes eq: "f \<equiv> C (nrec.fixp_fun (\<lambda>f. U (F (C f))))"
  assumes inverse2: "\<And>f. U (C f) = f"
  assumes step: "\<And>f x z. (\<And>x. U f x = U f x; Q x z) \<Longrightarrow> Q (U (F (C f))) z"
 (* assumes defined: "RETURN y \<le> U (C f) x"*)
  assumes Q: "\<And>x z. Q x z \<longleftrightarrow> z = U f x \<and> U f x \<le> SPEC (P x)"
  shows "Q x z" oops
  (*using step defined
    nrec.fixp_induct_uc[of U F C, OF mono eq inverse2 nrec_admissible]
  unfolding Q oops (*
  by blast*)*)

lemma fixp_induct_nrec':
  fixes F :: "'c \<Rightarrow> 'c" and
    U :: "'c \<Rightarrow> 'b \<Rightarrow> 'a nres" and
    C :: "('b \<Rightarrow> 'a nres) \<Rightarrow> 'c" and
    P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono: "\<And>x. nrec_mono (\<lambda>f. U (F (C f)) x)"
  assumes eq: "f \<equiv> C (nrec_ffix (\<lambda>f. U (F (C f))))"
  assumes inverse2: "\<And>f. U (C f) = f"
  assumes step: "\<And>f x0. (\<And>x0. U f x0 \<le> SPEC (P x0)) 
    \<Longrightarrow> U (F f) x0 \<le> SPEC (P x0)"
  assumes defined: "RETURN y \<le> U f x"
  shows "P x y"
proof -
  note defined
  also have "\<forall>x0. U f x0 \<le> SPEC (P x0)"
    apply (rule nrec.fixp_induct_uc[of U F C, OF mono eq inverse2 
      nrec_admissible])
    using step by blast
  hence "U f x \<le> SPEC (P x)" by simp
  finally show "P x y" by auto
qed
*)    
(* TODO/FIXME: Induction rule seems not to work here ! 
    Function package expects induction rule where conclusion is a binary 
    predicate as free variable.
*)

declaration \<open>Partial_Function.init "nrec" @{term nrec.fixp_fun}
  @{term nrec.mono_body} @{thm nrec.fixp_rule_uc} @{thm nrec.fixp_induct_uc}
  (*SOME @{thm fixp_induct_nrec}*) (NONE)\<close>

lemma bind_mono_pfun[partial_function_mono]:
  fixes C :: "'a \<Rightarrow> ('b \<Rightarrow> 'c nres) \<Rightarrow> ('d nres)"
  shows
  "\<lbrakk> monotone (fun_ord (\<le>)) (\<le>) B; 
    \<And>y. monotone (fun_ord (\<le>)) (\<le>) (\<lambda>f. C y f) \<rbrakk> \<Longrightarrow> 
     monotone (fun_ord (\<le>)) (\<le>) (\<lambda>f. bind (B f) (\<lambda>y. C y f))"
  apply rule
  apply (rule Refine_Basic.bind_mono)
  apply (blast dest: monotoneD)+
  done


subsection \<open>Deterministic Result Monad\<close>

interpretation drec:
  partial_function_definitions "(\<le>)" "Sup::'a dres set \<Rightarrow> 'a dres"
  by unfold_locales (auto simp add: Sup_upper Sup_least)

lemma drec_admissible: "drec.admissible (\<lambda>(f::'a \<Rightarrow> 'b dres).
  (\<forall>x. P x \<longrightarrow> 
    (f x \<noteq> dFAIL \<and> 
    (\<forall>r. f x = dRETURN r \<longrightarrow> Q x r))))"
proof -
  have [simp]: "fun_ord ((\<le>) ::'b dres \<Rightarrow> _ \<Rightarrow> _) = (\<le>)"
    apply (intro ext)
    unfolding fun_ord_def le_fun_def
    by (rule refl)

  have [simp]: "\<And>A x. {y. \<exists>f\<in>A. y = f x} = (\<lambda>f. f x)`A" by auto

  show ?thesis
    apply (rule ccpo.admissibleI)
    apply (unfold fun_lub_def)
    apply clarsimp
    apply (drule_tac x=x in point_chainI)
    apply (erule dres_Sup_chain_cases)
    apply auto
    apply (metis (poly_guards_query) SUP_bot_conv(1))
    apply (metis (poly_guards_query) SUP_bot_conv(1))
    apply metis
    done
qed

declaration \<open>Partial_Function.init "drec" @{term drec.fixp_fun}
  @{term drec.mono_body} @{thm drec.fixp_rule_uc} @{thm drec.fixp_induct_uc} 
  NONE\<close>

lemma drec_bind_mono_pfun[partial_function_mono]:
  fixes C :: "'a \<Rightarrow> ('b \<Rightarrow> 'c dres) \<Rightarrow> ('d dres)"
  shows
  "\<lbrakk> monotone (fun_ord (\<le>)) (\<le>) B; 
    \<And>y. monotone (fun_ord (\<le>)) (\<le>) (\<lambda>f. C y f) \<rbrakk> \<Longrightarrow> 
     monotone (fun_ord (\<le>)) (\<le>) (\<lambda>f. dbind (B f) (\<lambda>y. C y f))"
  apply rule
  apply (rule dbind_mono)
  apply (blast dest: monotoneD)+
  done

end
