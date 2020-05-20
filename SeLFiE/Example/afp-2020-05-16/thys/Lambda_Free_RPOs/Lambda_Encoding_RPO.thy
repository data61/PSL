(*  Title:       Properties of Lambda-Free RPO on the Lambda Encoding
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2019
    Maintainer:  Jasmin Blanchette <j.c.blanchette at vu.nl>
*)

section \<open>Properties of Lambda-Free RPO on the Lambda Encoding\<close>

theory Lambda_Encoding_RPO
imports Lambda_Encoding Lambda_Free_RPO_Std
begin

text \<open>
This theory explores the properties of the \<open>\<lambda>\<close>-free RPO on the proposed encoding of \<open>\<lambda>\<close>-expressions.
\<close>

locale rpo_lambda_encoding = rpo _ _ _ arity_sym arity_var + lambda_encoding arity_sym arity_var
  for
    arity_sym :: "'s \<Rightarrow> enat" and
    arity_var :: "'v \<Rightarrow> enat"
begin

lemma subst_db_Suc_ge: "subst_db (Suc i) x t2 \<ge>\<^sub>t subst_db i x t2"
  sorry

lemma gt_subst_db:
  assumes
    ary_ge: "arity_sym (db i) \<ge> arity_var x" and
    t_gt_s: "t >\<^sub>t s"
  shows "(\<And>i. subst_db i x t >\<^sub>t subst_db i x s)"
  using t_gt_s
proof induct
  case gt_sub_t_s: (gt_sub t s)

  have t_app: "is_App (subst_db i x t)"
    by (metis gt_sub_t_s.hyps(1) subst_db.simps(3) tm.collapse(2) tm.disc(2))

  obtain t1 t2 where t: "t = App t1 t2"
    by (metis gt_sub_t_s.hyps(1) tm.collapse(2))

  {
    assume "t1 >\<^sub>t s \<and> (\<forall>xa. subst_db xa x t1 >\<^sub>t subst_db xa x s)"
    hence "fun (subst_db i x t) \<ge>\<^sub>t subst_db i x s"
      unfolding t by auto
  }
  moreover
  {
    assume h: "t2 >\<^sub>t s \<and> (\<forall>xa. subst_db xa x t2 >\<^sub>t subst_db xa x s)"

    have "arg (subst_db i x t) \<ge>\<^sub>t subst_db i x s"
      using h
      unfolding t
      apply auto
      using gt_trans subst_db_Suc_ge by fastforce
  }
  moreover
  {
    assume "t2 = s"
    then have "arg (subst_db i x t) \<ge>\<^sub>t subst_db i x s"
      unfolding t by (auto intro!: subst_db_Suc_ge)
  }
  ultimately show ?case
    using gt_sub[OF t_app] gt_sub_t_s.hyps(2) unfolding t by auto
next
  case gt_diff_t_s: (gt_diff t s)
  show ?case
    apply (rule gt_diff)
    sorry
next
  case gt_same_t_s: (gt_same t s)
  note hd_t_eq_s = this(1) and chksubs_t_s = this(2) and ext_t_s = this(3)
  show ?case
    apply (rule gt_same)
      apply (rule tm.inject(1)[THEN iffD1])
      apply (unfold Hd_head_subst_db hd_t_eq_s)
      apply (rule refl)
    using chksubs_t_s
    unfolding chksubs_def
    apply (cases s)
      apply auto
      apply (case_tac x1)
       apply auto
    defer
    unfolding args_subst_db
    apply auto
    thm extf_map
    apply (rule extf_map)


    using ext_t_s

(*
    apply (rule chksubs_mono[THEN predicate2D])
    defer
    thm  chksubs_t_s

    apply (rule chksubs_t_s)
    using chksubs_t_s
*)

    sorry
qed

end

end
