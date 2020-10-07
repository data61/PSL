(*  Title:      While_Combinator_Exts.thy
    Author:     Denis Lohner
*)

section \<open>Code Generation\<close>
subsection \<open>While Combinator Extensions\<close>

theory While_Combinator_Exts imports
  "HOL-Library.While_Combinator"
begin
lemma while_option_None_invD:
  assumes "while_option b c s = None" and "wf r"
  and "I s" and "\<And>s. \<lbrakk> I s; b s \<rbrakk> \<Longrightarrow> I (c s)"
  and "\<And>s. \<lbrakk> I s; b s \<rbrakk> \<Longrightarrow> (c s, s ) \<in> r"
  shows "False"
  using assms
  by -(drule wf_rel_while_option_Some [of r I b c], auto)

lemma while_option_NoneD:
  assumes "while_option b c s = None"
  and "wf r" and "\<And>s. b s \<Longrightarrow> (c s, s) \<in> r"
  shows "False"
  using assms
  by (blast intro: while_option_None_invD)

lemma while_option_sim:
  assumes start: "R (Some s1) (Some s2)"
  and cond: "\<And>s1 s2. \<lbrakk> R (Some s1) (Some s2); I s1 \<rbrakk> \<Longrightarrow> b1 s1 = b2 s2"
  and step : "\<And>s1 s2. \<lbrakk> R (Some s1) (Some s2); I s1; b1 s1 \<rbrakk> \<Longrightarrow> R (Some (c1 s1)) (Some (c2 s2))"
  and diverge: "R None None"
  and inv_start: "I s1"
  and inv_step: "\<And>s1. \<lbrakk> I s1; b1 s1 \<rbrakk> \<Longrightarrow> I (c1 s1)"
  shows "R (while_option b1 c1 s1) (while_option b2 c2 s2)"
proof -
  { fix k
    assume "\<forall>k' < k. b1 ((c1 ^^ k') s1)"
    with start cond step inv_start inv_step
    have "b1 ((c1 ^^ k) s1) = b2 ((c2 ^^ k) s2)" and "I ((c1 ^^ k) s1)"
      and "R (Some ((c1 ^^ k) s1)) (Some ((c2 ^^ k) s2))"
      by (induction k) auto
  }
  moreover
  { fix k
    assume "\<not> b1 ((c1 ^^ k) s1)"
    hence "\<forall>k' < LEAST k. \<not> b1 ((c1 ^^ k) s1). b1 ((c1 ^^ k') s1)"
      by (metis (lifting) not_less_Least)
  }
  moreover
  { fix k
    assume "\<not> b2 ((c2 ^^ k) s2)"
    hence "\<forall>k' < LEAST k. \<not> b2 ((c2 ^^ k) s2). b2 ((c2 ^^ k') s2)"
      by (metis (lifting) not_less_Least)
  }
  moreover
  {
    assume "\<exists>k. \<not> b1 ((c1 ^^ k) s1)"
      and "\<exists>k. \<not> b2 ((c2 ^^ k) s2)"
    hence not_cond_Least: "\<not> b1 ((c1 ^^ (LEAST k. \<not> b1 ((c1 ^^ k) s1))) s1)"
      "\<not> b2 ((c2 ^^ (LEAST k. \<not> b2 ((c2 ^^ k) s2))) s2)"
      by -(drule LeastI_ex, assumption)+
    { fix k
      assume "\<forall>k' < k. b1 ((c1 ^^ k') s1)"
      with calculation(1) dual_order.strict_trans
      have "\<forall>k' < k. b2 ((c2 ^^ k') s2)"
        by blast
    }
    hence "(LEAST k'. \<not> b1 ((c1 ^^ k') s1)) = (LEAST k'. \<not> b2 ((c2 ^^ k') s2))"
      by (metis (no_types, lifting) not_cond_Least calculation(1,4,5) less_linear)
    with calculation(3,4)
    have "R (Some ((c1 ^^ (LEAST k. \<not> b1 ((c1 ^^ k) s1))) s1))
      (Some ((c2 ^^ (LEAST k. \<not> b2 ((c2 ^^ k) s2))) s2))"
      by auto
  }
  ultimately show ?thesis using diverge
    unfolding while_option_def
    apply (split if_split)
    apply (rule conjI)
     apply (split if_split)
     apply metis
    apply (split if_split)
    by (metis (lifting) LeastI_ex)
qed

end
