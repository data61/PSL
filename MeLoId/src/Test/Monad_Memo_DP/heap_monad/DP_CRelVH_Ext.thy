theory DP_CRelVH_Ext
imports DP_CRelVH
begin
context dp_consistency_heap begin

definition "crel_vs1 R v f \<equiv>
  \<forall>heap. P heap \<longrightarrow>
    (case execute f heap of None \<Rightarrow> False | Some (v', heap') \<Rightarrow> P heap' \<and> (state_dp_consistency.cmem heap \<longrightarrow> R v v' \<and> state_dp_consistency.cmem heap'))
"

lemma crel_vs1_execute_None:
  False if "crel_vs1 R a b" "execute b heap = None" "P heap"
  using that unfolding crel_vs1_def by auto

lemma crel_vs1_execute_Some:
  assumes "crel_vs1 R a b" "P heap"
  obtains x heap' where "execute b heap = Some (x, heap')" "P heap'"
  using assms unfolding crel_vs1_def by (cases "execute b heap") auto

lemma crel_vs1_executeD:
  assumes "crel_vs1 R a b" "P heap" "state_dp_consistency.cmem heap"
  obtains x heap' where "execute b heap = Some (x, heap')" "P heap'" "state_dp_consistency.cmem heap'" "R a x"
  using assms unfolding crel_vs1_def by (cases "execute b heap") auto

lemma rel_state_state_of:
  "rel_state op = (state_of b) b" if "crel_vs1 R a b"
  unfolding rel_state_def state_of_def
  by (auto split: option.split elim: crel_vs1_execute_Some[OF that])

lemma crel_vs1_state_of:
  "state_dp_consistency.crel_vs R a (state_of b)" if "crel_vs1 R a b"
  unfolding state_dp_consistency.crel_vs_def state_of_def by (auto elim: crel_vs1_executeD[OF that])

lemma crel_vs1_alt_def:
  "crel_vs1 R = (state_dp_consistency.crel_vs R OO rel_state (op =))"
proof (intro ext)
  fix a b
  have "(state_dp_consistency.crel_vs R OO rel_state (op =)) a b" if "crel_vs1 R a b"
    using that by - (rule relcomppI; erule crel_vs1_state_of rel_state_state_of)
  moreover have "crel_vs1 R a b" if "(state_dp_consistency.crel_vs R OO rel_state (op =)) a b"
    using that by (auto 4 3 elim: state_dp_consistency.crel_vs_elim rel_state_elim simp: crel_vs1_def)
  ultimately show "crel_vs1 R a b = (state_dp_consistency.crel_vs R OO rel_state (op =)) a b" ..
qed

context
  includes lifting_syntax
begin

lemma transfer_return1[transfer_rule]:
  "(R ===> crel_vs1 R) Wrap return"
  unfolding crel_vs1_alt_def Wrap_def by (rule rel_fun_comp1 state_dp_consistency.return_transfer[unfolded Wrap_def] transfer_return)+ auto

lemma crel_vs_return1:
  "\<lbrakk>R x y\<rbrakk> \<Longrightarrow> crel_vs1 R (Wrap x) (return y)"
  by (rule transfer_return1[unfolded rel_fun_def, rule_format])
term 0 (**)

lemma crel_vs_rel_state:
  "(R0 ===> state_dp_consistency.crel_vs R1) x (state_of o y)" if "(R0 ===> state_dp_consistency.crel_vs R1 OO rel_state op =) x y"
  using that
  unfolding state_of_def
  apply -
  apply (rule rel_funI)
  apply (drule rel_funD, assumption)
  apply (erule relcomppE)
  apply auto
  apply (rule state_dp_consistency.crel_vs_intro)
  apply auto
   apply (erule rel_state_elim, assumption)
    apply (erule state_dp_consistency.crel_vs_elim)
      apply assumption+
    apply simp
  subgoal premises prems for x' y' b M v' M'
  proof -
    from prems(2,3) have "crel_vs1 R1 (x x') (y y')"
      unfolding crel_vs1_alt_def by (rule relcomppI)
    with prems show ?thesis
      by (auto elim: crel_vs1_executeD)
  qed
  subgoal premises prems for x' y' b M v' M'
  proof -
    from prems(2,3) have "crel_vs1 R1 (x x') (y y')"
      unfolding crel_vs1_alt_def by (rule relcomppI)
    with prems show ?thesis
      by (auto elim: crel_vs1_executeD)
  qed
  done

lemma bind_transfer1:
  "(crel_vs1 R0 ===> (R0 ===> crel_vs1 R1) ===> crel_vs1 R1) (\<lambda>v f. f v) (op \<bind>)"
  if "\<And> x. R0 x x"
  unfolding crel_vs1_alt_def
  apply (rule rel_fun_comp2')
    apply (rule state_dp_consistency.bind_transfer)
   apply (rule transfer_bind)
  apply (drule rel_fun_relcompp)
  apply (erule rel_fun_mono)
   defer
   apply assumption
  apply (intro impI relcomppI)
   apply (erule crel_vs_rel_state)
  by (auto 4 4 dest: rel_funD intro: that elim: rel_state_state_of simp: crel_vs1_alt_def[symmetric])

lemma fun_app_transfer[transfer_rule]:
  "(crel_vs1 (R0 ===> crel_vs1 R1) ===> crel_vs1 R0 ===> crel_vs1 R1) App Heap_Monad_Ext.fun_app_lifted"
  unfolding App_def Heap_Monad_Ext.fun_app_lifted_def
  oops
end (* Lifting Syntax *)

end (* Dynamic Programming Problem *)

end