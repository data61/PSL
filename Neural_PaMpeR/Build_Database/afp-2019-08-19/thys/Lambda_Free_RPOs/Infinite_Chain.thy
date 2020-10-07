(*  Title:       Infinite (Non-Well-Founded) Chains
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Infinite (Non-Well-Founded) Chains\<close>

theory Infinite_Chain
imports Lambda_Free_Util
begin

text \<open>
This theory defines the concept of a minimal bad (or non-well-founded)
infinite chain, as found in the term rewriting literature to prove the
well-foundedness of syntactic term orders.
\<close>

context
  fixes p :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

definition inf_chain :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "inf_chain f \<longleftrightarrow> (\<forall>i. p (f i) (f (Suc i)))"

lemma wfP_iff_no_inf_chain: "wfP (\<lambda>x y. p y x) \<longleftrightarrow> (\<nexists>f. inf_chain f)"
  unfolding wfP_def wf_iff_no_infinite_down_chain inf_chain_def by simp

lemma inf_chain_offset: "inf_chain f \<Longrightarrow> inf_chain (\<lambda>j. f (j + i))"
  unfolding inf_chain_def by simp

definition bad :: "'a \<Rightarrow> bool" where
  "bad x \<longleftrightarrow> (\<exists>f. inf_chain f \<and> f 0 = x)"

lemma inf_chain_bad:
  assumes bad_f: "inf_chain f"
  shows "bad (f i)"
  unfolding bad_def by (rule exI[of _ "\<lambda>j. f (j + i)"]) (simp add: inf_chain_offset[OF bad_f])

context
  fixes gt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes wf: "wf {(x, y). gt y x}"
begin

primrec worst_chain :: "nat \<Rightarrow> 'a" where
  "worst_chain 0 = (SOME x. bad x \<and> (\<forall>y. bad y \<longrightarrow> \<not> gt x y))"
| "worst_chain (Suc i) = (SOME x. bad x \<and> p (worst_chain i) x \<and>
     (\<forall>y. bad y \<and> p (worst_chain i) y \<longrightarrow> \<not> gt x y))"

declare worst_chain.simps[simp del]

context
  fixes x :: 'a
  assumes x_bad: "bad x"
begin

lemma
  bad_worst_chain_0: "bad (worst_chain 0)" and
  min_worst_chain_0: "\<not> gt (worst_chain 0) x"
proof -
  obtain y where "bad y \<and> (\<forall>z. bad z \<longrightarrow> \<not> gt y z)"
    using wf_exists_minimal[OF wf, of bad, OF x_bad] by force
  hence "bad (worst_chain 0) \<and> (\<forall>z. bad z \<longrightarrow> \<not> gt (worst_chain 0) z)"
    unfolding worst_chain.simps by (rule someI)
  thus "bad (worst_chain 0)" and "\<not> gt (worst_chain 0) x"
    using x_bad by blast+
qed

lemma
  bad_worst_chain_Suc: "bad (worst_chain (Suc i))" and
  worst_chain_pred: "p (worst_chain i) (worst_chain (Suc i))" and
  min_worst_chain_Suc: "p (worst_chain i) x \<Longrightarrow> \<not> gt (worst_chain (Suc i)) x"
proof (induct i rule: less_induct)
  case (less i)

  have "bad (worst_chain i)"
  proof (cases i)
    case 0
    thus ?thesis
      using bad_worst_chain_0 by simp
  next
    case (Suc j)
    thus ?thesis
      using less(1) by blast
  qed
  then obtain fa where fa_bad: "inf_chain fa" and fa_0: "fa 0 = worst_chain i"
    unfolding bad_def by blast

  have "\<exists>s0. bad s0 \<and> p (worst_chain i) s0"
  proof (intro exI conjI)
    let ?y0 = "fa (Suc 0)"

    show "bad ?y0"
      unfolding bad_def by (auto intro: exI[of _ "\<lambda>i. fa (Suc i)"] inf_chain_offset[OF fa_bad])
    show "p (worst_chain i) ?y0"
      using fa_bad[unfolded inf_chain_def] fa_0 by metis
  qed
  then obtain y0 where y0: "bad y0 \<and> p (worst_chain i) y0"
    by blast

  obtain y1 where
    y1: "bad y1 \<and> p (worst_chain i) y1 \<and> (\<forall>z. bad z \<and> p (worst_chain i) z \<longrightarrow> \<not> gt y1 z)"
    using wf_exists_minimal[OF wf, of "\<lambda>y. bad y \<and> p (worst_chain i) y", OF y0] by force

  let ?y = "worst_chain (Suc i)"

  have conj: "bad ?y \<and> p (worst_chain i) ?y \<and> (\<forall>z. bad z \<and> p (worst_chain i) z \<longrightarrow> \<not> gt ?y z)"
    unfolding worst_chain.simps using y1 by (rule someI)

  show "bad ?y"
    by (rule conj[THEN conjunct1])
  show "p (worst_chain i) ?y"
    by (rule conj[THEN conjunct2, THEN conjunct1])
  show "p (worst_chain i) x \<Longrightarrow> \<not> gt ?y x"
    using x_bad conj[THEN conjunct2, THEN conjunct2, rule_format] by meson
qed

lemma bad_worst_chain: "bad (worst_chain i)"
  by (cases i) (auto intro: bad_worst_chain_0 bad_worst_chain_Suc)

lemma worst_chain_bad: "inf_chain worst_chain"
  unfolding inf_chain_def using worst_chain_pred by metis

end

context
  fixes x :: 'a
  assumes
    x_bad: "bad x" and
    p_trans: "\<And>z y x. p z y \<Longrightarrow> p y x \<Longrightarrow> p z x"
begin

lemma worst_chain_not_gt: "\<not> gt (worst_chain i) (worst_chain (Suc i))" for i
proof (cases i)
  case 0
  show ?thesis
    unfolding 0 by (rule min_worst_chain_0[OF inf_chain_bad[OF worst_chain_bad[OF x_bad]]])
next
  case Suc
  show ?thesis
    unfolding Suc
  by (rule min_worst_chain_Suc[OF inf_chain_bad[OF worst_chain_bad[OF x_bad]]])
    (rule p_trans[OF worst_chain_pred[OF x_bad] worst_chain_pred[OF x_bad]])
qed

end

end

end

lemma inf_chain_subset: "inf_chain p f \<Longrightarrow> p \<le> q \<Longrightarrow> inf_chain q f"
  unfolding inf_chain_def by blast

hide_fact (open) bad_worst_chain_0 bad_worst_chain_Suc

end
