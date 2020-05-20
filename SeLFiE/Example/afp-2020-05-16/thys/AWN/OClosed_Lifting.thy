(*  Title:       OClosed_Lifting.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Lifting rules for (open) closed networks"

theory OClosed_Lifting
imports OPnet_Lifting
begin

lemma trans_fst_oclosed_fst1 [dest]:
  "(s, connect(i, i'), s') \<in> ocnet_sos (trans p) \<Longrightarrow> (s, connect(i, i'), s') \<in> trans p"
  by (metis prod.exhaust oconnect_completeTE)

lemma trans_fst_oclosed_fst2 [dest]:
  "(s, disconnect(i, i'), s') \<in> ocnet_sos (trans p) \<Longrightarrow> (s, disconnect(i, i'), s') \<in> trans p"
  by (metis prod.exhaust odisconnect_completeTE)

lemma trans_fst_oclosed_fst3 [dest]:
  "(s, i:deliver(d), s') \<in> ocnet_sos (trans p) \<Longrightarrow>      (s, i:deliver(d), s') \<in> trans p"
  by (metis prod.exhaust odeliver_completeTE)

lemma oclosed_oreachable_inclosed:
  assumes "(\<sigma>, \<zeta>) \<in> oreachable (oclosed (opnet np p)) (\<lambda>_ _ _. True) U"
    shows "(\<sigma>, \<zeta>) \<in> oreachable (opnet np p) (otherwith ((=)) (net_tree_ips p) inoclosed) U"
    (is "_ \<in> oreachable _ ?owS _")
  using assms proof (induction rule: oreachable_pair_induct)
    fix \<sigma> \<zeta>
    assume "(\<sigma>, \<zeta>) \<in> init (oclosed (opnet np p))"
    hence "(\<sigma>, \<zeta>) \<in> init (opnet np p)" by simp
    thus "(\<sigma>, \<zeta>) \<in> oreachable (opnet np p) ?owS U" ..
  next
    fix \<sigma> \<zeta> \<sigma>'
    assume "(\<sigma>, \<zeta>) \<in> oreachable (opnet np p) ?owS U"
       and "U \<sigma> \<sigma>'"
    thus "(\<sigma>', \<zeta>) \<in> oreachable (opnet np p) ?owS U"
      by - (rule oreachable_other')
  next
    fix \<sigma> \<zeta> \<sigma>' \<zeta>' a
    assume zor: "(\<sigma>, \<zeta>) \<in> oreachable (opnet np p) ?owS U"
       and ztr: "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (oclosed (opnet np p))"
    from this(1) have [simp]: "net_ips \<zeta> = net_tree_ips p"
      by (rule opnet_net_ips_net_tree_ips)
    from ztr have "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> ocnet_sos (trans (opnet np p))" by simp
    thus "(\<sigma>', \<zeta>') \<in> oreachable (opnet np p) ?owS U"
    proof cases
      fix i K d di
      assume "a = i:newpkt(d, di)"
         and tr: "((\<sigma>, \<zeta>), {i}\<not>K:arrive(msg_class.newpkt (d, di)), (\<sigma>', \<zeta>')) \<in> trans (opnet np p)"
         and "\<forall>j. j \<notin> net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
      from this(3) have "\<forall>j. j \<notin> net_tree_ips p \<longrightarrow> \<sigma>' j = \<sigma> j"
        using \<open>net_ips \<zeta> = net_tree_ips p\<close> by auto
      hence "otherwith ((=)) (net_tree_ips p) inoclosed \<sigma> \<sigma>' ({i}\<not>K:arrive(msg_class.newpkt (d, di)))"
        by auto
      with zor tr show ?thesis
        by - (rule oreachable_local')
    next
      assume "a = \<tau>"
         and tr: "((\<sigma>, \<zeta>), \<tau>, (\<sigma>', \<zeta>')) \<in> trans (opnet np p)"
         and "\<forall>j. j \<notin> net_ips \<zeta> \<longrightarrow> \<sigma>' j = \<sigma> j"
      from this(3) have "\<forall>j. j \<notin> net_tree_ips p \<longrightarrow> \<sigma>' j = \<sigma> j"
        using \<open>net_ips \<zeta> = net_tree_ips p\<close> by auto
      hence "otherwith ((=)) (net_tree_ips p) inoclosed \<sigma> \<sigma>' \<tau>"
        by auto
      with zor tr show ?thesis by - (rule oreachable_local')
    qed (insert \<open>net_ips \<zeta> = net_tree_ips p\<close>,
         auto elim!: oreachable_local' [OF zor])
  qed

lemma oclosed_oreachable_oreachable [elim]:
  assumes "(\<sigma>, \<zeta>) \<in> oreachable (oclosed (opnet onp p)) (\<lambda>_ _ _. True) U"
    shows "(\<sigma>, \<zeta>) \<in> oreachable (opnet onp p) (\<lambda>_ _ _. True) U"
  using assms by (rule oclosed_oreachable_inclosed [THEN oreachable_weakenE]) simp

lemma inclosed_closed [intro]:
  assumes cinv: "opnet np p \<Turnstile> (otherwith ((=)) (net_tree_ips p) inoclosed, U \<rightarrow>) P"
    shows "oclosed (opnet np p) \<Turnstile> (\<lambda>_ _ _. True, U \<rightarrow>) P"
  using assms unfolding oinvariant_def
  by (clarsimp dest!: oclosed_oreachable_inclosed)

end
