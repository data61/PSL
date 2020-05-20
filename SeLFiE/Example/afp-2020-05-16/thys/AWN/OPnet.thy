(*  Title:       OPnet.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Lemmas for open partial networks"

theory OPnet
imports OAWN_SOS OInvariants
begin

text \<open>
  These lemmas mostly concern the preservation of node structure by @{term opnet_sos} transitions.
\<close>

lemma opnet_maintains_dom:
  assumes "((\<sigma>, ns), a, (\<sigma>', ns')) \<in> trans (opnet np p)"
    shows "net_ips ns = net_ips ns'"
  using assms proof (induction p arbitrary: \<sigma> ns a \<sigma>' ns')
    fix i R \<sigma> ns a \<sigma>' ns'
    assume "((\<sigma>, ns), a, (\<sigma>', ns')) \<in> trans (opnet np \<langle>i; R\<rangle>)"
    hence "((\<sigma>, ns), a, (\<sigma>', ns')) \<in> onode_sos (trans (np i))" ..
    thus "net_ips ns = net_ips ns'"
      by (simp add: net_ips_is_dom_netmap)
         (erule onode_sos.cases, simp_all)
  next
    fix p1 p2 \<sigma> ns a \<sigma>' ns'
    assume "\<And>\<sigma> ns a \<sigma>' ns'. ((\<sigma>, ns), a, (\<sigma>', ns')) \<in> trans (opnet np p1) \<Longrightarrow> net_ips ns = net_ips ns'"
       and "\<And>\<sigma> ns a \<sigma>' ns'. ((\<sigma>, ns), a, (\<sigma>', ns')) \<in> trans (opnet np p2) \<Longrightarrow> net_ips ns = net_ips ns'"
       and "((\<sigma>, ns), a, (\<sigma>', ns')) \<in> trans (opnet np (p1 \<parallel> p2))"
    thus "net_ips ns = net_ips ns'"
      by simp (erule opnet_sos.cases, simp_all)
  qed

lemma opnet_net_ips_net_tree_ips:
  assumes "(\<sigma>, ns) \<in> oreachable (opnet np p) S U"
    shows "net_ips ns = net_tree_ips p"
  using assms proof (induction rule: oreachable_pair_induct)
    fix \<sigma> s
    assume "(\<sigma>, s) \<in> init (opnet np p)"
    thus "net_ips s = net_tree_ips p"
    proof (induction p arbitrary: \<sigma> s)
      fix p1 p2 \<sigma> s
      assume IH1: "(\<And>\<sigma> s. (\<sigma>, s) \<in> init (opnet np p1) \<Longrightarrow> net_ips s = net_tree_ips p1)"
         and IH2: "(\<And>\<sigma> s. (\<sigma>, s) \<in> init (opnet np p2) \<Longrightarrow> net_ips s = net_tree_ips p2)"
         and "(\<sigma>, s) \<in> init (opnet np (p1 \<parallel> p2))"
      thus "net_ips s = net_tree_ips (p1 \<parallel> p2)"
        by (clarsimp simp add: net_ips_is_dom_netmap)
           (metis Un_commute)
    qed (clarsimp simp add: onode_comps)
  next
    fix \<sigma> s \<sigma>' s' a
    assume "(\<sigma>, s) \<in> oreachable (opnet np p) S U"
       and "net_ips s = net_tree_ips p"
       and "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans (opnet np p)"
       and "S \<sigma> \<sigma>' a"
    thus "net_ips s' = net_tree_ips p"
      by (simp add: net_ips_is_dom_netmap)
         (metis net_ips_is_dom_netmap opnet_maintains_dom)
  qed simp

lemma opnet_net_ips_net_tree_ips_init:
  assumes "(\<sigma>, ns) \<in> init (opnet np p)"
    shows "net_ips ns = net_tree_ips p"
  using assms(1) by (rule oreachable_init [THEN opnet_net_ips_net_tree_ips])

lemma opartial_net_preserves_subnets:
  assumes "((\<sigma>, SubnetS s t), a, (\<sigma>', st')) \<in> opnet_sos (trans (opnet np p1)) (trans (opnet np p2))"
    shows "\<exists>s' t'. st' = SubnetS s' t'"
  using assms by cases simp_all

lemma net_par_oreachable_is_subnet:
  assumes "(\<sigma>, st) \<in> oreachable (opnet np (p1 \<parallel> p2)) S U"
    shows "\<exists>s t. st = SubnetS s t"
  proof -
    define p where "p = (\<sigma>, st)"
    with assms have "p \<in> oreachable (opnet np (p1 \<parallel> p2)) S U" by simp
    hence "\<exists>\<sigma> s t. p = (\<sigma>, SubnetS s t)"
      by induct (auto dest!: opartial_net_preserves_subnets)
    with p_def show ?thesis by simp
  qed

end
