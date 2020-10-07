section \<open>Prefixes on Coinductive Lists\<close>

theory LList_Prefixes
imports
  Word_Prefixes
  "../Extensions/Coinductive_List_Extensions"
begin

  lemma unfold_stream_siterate_smap: "unfold_stream f g = smap f \<circ> siterate g"
    by (rule, coinduction, auto) (metis unfold_stream_eq_SCons)+

  lemma lappend_stream_of_llist:
    assumes "lfinite u"
    shows "stream_of_llist (u $ v) = list_of u @- stream_of_llist v"
    using assms unfolding stream_of_llist_def by induct auto

  lemma llist_of_inf_llist_prefix[intro]: "u \<le>\<^sub>F\<^sub>I v \<Longrightarrow> llist_of u \<le> llist_of_stream v"
    by (metis lappend_llist_of_stream_conv_shift le_llist_conv_lprefix lprefix_lappend prefix_fininfE)
  lemma prefix_llist_of_inf_llist[intro]: "lfinite u \<Longrightarrow> u \<le> v \<Longrightarrow> list_of u \<le>\<^sub>F\<^sub>I stream_of_llist v"
    by (metis lappend_stream_of_llist le_llist_conv_lprefix lprefix_conv_lappend prefix_fininfI)

  lemma lproject_prefix_limit_chain:
    assumes "chain w" "\<And> k. lproject A (llist_of (w k)) \<le> x"
    shows "lproject A (llist_of_stream (limit w)) \<le> x"
  proof (rule lproject_prefix_limit')
    fix k
    obtain l where 1: "k < length (w l)" using assms(1) by rule
    show "\<exists> v \<le> llist_of_stream (limit w). enat k < llength v \<and> lproject A v \<le> x"
    proof (intro exI conjI)
      show "llist_of (w l) \<le> llist_of_stream (limit w)"
        using llist_of_inf_llist_prefix chain_prefix_limit assms(1) by this
      show "enat k < llength (llist_of (w l))" using 1 by simp
      show "lproject A (llist_of (w l)) \<le> x" using assms(2) by this
    qed
  qed
  lemma lproject_eq_limit_chain:
    assumes "chain u" "chain v" "\<And> k. project A (u k) = project A (v k)"
    shows "lproject A (llist_of_stream (limit u)) = lproject A (llist_of_stream (limit v))"
  proof (rule antisym)
    show "lproject A (llist_of_stream (limit u)) \<le> lproject A (llist_of_stream (limit v))"
    proof (rule lproject_prefix_limit_chain)
      show "chain u" using assms(1) by this
    next
      fix k
      have "lproject A (llist_of (u k)) = lproject A (llist_of (v k))" using assms(3) by simp
      also have "\<dots> \<le> lproject A (llist_of_stream (limit v))" using chain_prefix_limit assms(2) by blast
      finally show "lproject A (llist_of (u k)) \<le> lproject A (llist_of_stream (limit v))" by this
    qed
    show "lproject A (llist_of_stream (limit v)) \<le> lproject A (llist_of_stream (limit u))"
    proof (rule lproject_prefix_limit_chain)
      show "chain v" using assms(2) by this
    next
      fix k
      have "lproject A (llist_of (v k)) = lproject A (llist_of (u k))" using assms(3) by simp
      also have "\<dots> \<le> lproject A (llist_of_stream (limit u))" using chain_prefix_limit assms(1) by blast
      finally show "lproject A (llist_of (v k)) \<le> lproject A (llist_of_stream (limit u))" by this
    qed
  qed

end