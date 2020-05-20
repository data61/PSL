theory ShortestPath
imports
  Graph_Theory.Graph_Theory
begin

section \<open>Shortest Path (with non-negative edge costs)\<close>
text\<open>The following theory is used in the verification of a certifying algorithm's checker for shortest path. For more information see \cite{FrameworkVerificationofCertifyingComputations}.\<close>

locale basic_sp = 
  fin_digraph +
  fixes dist :: "'a \<Rightarrow> ereal"
  fixes c :: "'b \<Rightarrow> real"
  fixes s :: "'a"
  assumes general_source_val: "dist s \<le> 0"
  assumes trian:
    "\<And>e. e \<in> arcs G \<Longrightarrow> 
      dist (head G e) \<le> dist (tail G e) + c e"

locale basic_just_sp = 
  basic_sp +
  fixes num :: "'a \<Rightarrow> enat"
  assumes just:
    "\<And>v. \<lbrakk>v \<in> verts G; v \<noteq> s; num v \<noteq> \<infinity>\<rbrakk> \<Longrightarrow>
      \<exists> e \<in> arcs G. v = head G e \<and>
        dist v = dist (tail G e) + c e  \<and>
        num v = num (tail G e) + (enat 1)"

locale shortest_path_pos_cost =
  basic_just_sp +
  assumes s_in_G: "s \<in> verts G"
  assumes tail_val: "dist s = 0"
  assumes no_path: "\<And>v. v \<in> verts G \<Longrightarrow> dist v = \<infinity> \<longleftrightarrow> num v = \<infinity>"
  assumes pos_cost: "\<And>e. e \<in> arcs G \<Longrightarrow> 0 \<le> c e"

locale basic_just_sp_pred = 
  basic_sp +
  fixes num :: "'a \<Rightarrow> enat"
  fixes pred :: "'a \<Rightarrow> 'b option"
  assumes just:
    "\<And>v. \<lbrakk>v \<in> verts G; v \<noteq> s; num v \<noteq> \<infinity>\<rbrakk> \<Longrightarrow>
      \<exists> e \<in> arcs G. 
        e = the (pred v) \<and> 
        v = head G e \<and>
        dist v = dist (tail G e) + c e  \<and>
        num v = num (tail G e) + (enat 1)"

sublocale basic_just_sp_pred \<subseteq> basic_just_sp  
using basic_just_sp_pred_axioms 
unfolding basic_just_sp_pred_def
   basic_just_sp_pred_axioms_def
by unfold_locales (blast)

locale shortest_path_pos_cost_pred =
  basic_just_sp_pred +
  assumes s_in_G: "s \<in> verts G"
  assumes tail_val: "dist s = 0"
  assumes no_path: "\<And>v. v \<in> verts G \<Longrightarrow> dist v = \<infinity> \<longleftrightarrow> num v = \<infinity>"
  assumes pos_cost: "\<And>e. e \<in> arcs G \<Longrightarrow> 0 \<le> c e"

sublocale shortest_path_pos_cost_pred \<subseteq> shortest_path_pos_cost
using shortest_path_pos_cost_pred_axioms 
by unfold_locales 
   (auto simp: shortest_path_pos_cost_pred_def 
   shortest_path_pos_cost_pred_axioms_def)

lemma tail_value_helper:
  assumes "hd p = last p"
  assumes "distinct p"
  assumes "p \<noteq> []"
  shows "p = [hd p]"
  by (metis assms distinct.simps(2) list.sel(1) neq_Nil_conv last_ConsR last_in_set)

lemma (in basic_sp) dist_le_cost:
  fixes v :: 'a
  fixes p :: "'b list" 
  assumes "awalk s p v"
  shows "dist v \<le> awalk_cost c p"
  using assms
  proof (induct "length p" arbitrary: p v)
  case 0
    hence "s = v" by auto
    thus ?case using 0(1) general_source_val
      by (metis awalk_cost_Nil length_0_conv zero_ereal_def)
  next
  case (Suc n)
    then obtain p' e where p'e: "p = p' @ [e]"
      by (cases p rule: rev_cases) auto
    then obtain u where ewu: "awalk s p' u \<and> awalk u [e] v" 
      using awalk_append_iff Suc(3) by simp
    then have du: "dist u \<le> ereal (awalk_cost c p')"
      using Suc p'e by simp
    from ewu have ust: "u = tail G e" and vta: "v = head G e"
      by auto
    then have "dist v \<le> dist u + c e"
      using ewu du ust trian[where e=e] by force
    with du have "dist v \<le> ereal (awalk_cost c p') + c e"
      by (metis add_right_mono order_trans)
    thus "dist v \<le> awalk_cost c p" 
      using awalk_cost_append p'e by simp
  qed

lemma (in fin_digraph) witness_path:
  assumes "\<mu> c s v = ereal r"
  shows "\<exists> p. apath s p v \<and> \<mu> c s v = awalk_cost c p"
proof -
  have sv: "s \<rightarrow>\<^sup>* v" 
    using shortest_path_inf[of s v c] assms by fastforce
  { 
    fix p assume "awalk s p v"
    then have no_neg_cyc: 
    "\<not> (\<exists>w q. awalk w q w \<and> w \<in> set (awalk_verts s p) \<and> awalk_cost c q < 0)"
      using neg_cycle_imp_inf_\<mu> assms by force
  }
  thus ?thesis using no_neg_cyc_reach_imp_path[OF sv] by presburger
qed

lemma (in basic_sp)  dist_le_\<mu>:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "dist v \<le> \<mu> c s v" 
proof (rule ccontr)
  assume nt: "\<not> ?thesis"
  show False
  proof (cases "\<mu> c s v")
    show "\<And>r. \<mu> c s v = ereal r \<Longrightarrow> False"
    proof -
      fix r assume r_asm: "\<mu> c s v = ereal r"
      hence sv: "s \<rightarrow>\<^sup>* v"
        using shortest_path_inf[where u=s and v=v and f=c] by auto
      obtain p where 
        "awalk s p v" 
        "\<mu> c s v = awalk_cost c p"
        using witness_path[OF r_asm] unfolding apath_def by force 
      thus False using nt dist_le_cost by simp
    qed
  next
    show "\<mu> c s v = \<infinity> \<Longrightarrow> False" using nt by simp
  next
    show "\<mu> c s v = - \<infinity> \<Longrightarrow> False" using dist_le_cost
    proof -
      assume asm: "\<mu> c s v = - \<infinity>"
      let ?C = "(\<lambda>x. ereal (awalk_cost c x)) ` {p. awalk s p v}"
      have "\<exists>x\<in> ?C. x < dist v"
        using nt unfolding \<mu>_def not_le INF_less_iff by simp
      then obtain p where  
        "awalk s p v" 
        "awalk_cost c p < dist v" 
        by force
      thus False using dist_le_cost by force
    qed
  qed
qed

lemma (in basic_just_sp) dist_ge_\<mu>:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "num v \<noteq> \<infinity>"
  assumes "dist v \<noteq> -\<infinity>"
  assumes "\<mu> c s s = ereal 0"
  assumes "dist s = 0"
  assumes "\<And>u. u\<in>verts G \<Longrightarrow> u\<noteq>s \<Longrightarrow>
            num u \<noteq> \<infinity> \<Longrightarrow> num u \<noteq> enat 0"
  shows "dist v \<ge> \<mu> c s v"
proof -
  obtain n where "enat n = num v" using assms(2) by force
  thus ?thesis using assms
  proof(induct n arbitrary: v) 
  case 0 thus ?case by (cases "v=s", auto)
  next
  case (Suc n)
    thus ?case 
    proof (cases "v=s") 
    case False
      obtain e where e_assms:
        "e \<in> arcs G" 
        "v = head G e"
        "dist v = dist (tail G e) + ereal (c e)" 
        "num v = num (tail G e) + enat 1" 
        using just[OF Suc(3) False Suc(4)] by blast
      then have nsinf:"num (tail G e) \<noteq> \<infinity>" 
        by (metis Suc(2) enat.simps(3) enat_1 plus_enat_simps(2))
      then have ns:"enat n = num (tail G e)" 
        using e_assms(4) Suc(2) by force
      have  ds: "dist (tail G e) = \<mu> c s (tail G e)" 
        using Suc(1)[OF ns tail_in_verts[OF e_assms(1)] nsinf] 
        Suc(5-8) e_assms(3) dist_le_\<mu>[OF tail_in_verts[OF e_assms(1)]] 
        by simp
      have dmuc:"dist v \<ge> \<mu> c s (tail G e) + ereal (c e)"
        using e_assms(3) ds  by auto
      thus ?thesis
      proof (cases "dist v = \<infinity>")
      case False
        have "arc_to_ends G e = (tail G e, v)" 
          unfolding arc_to_ends_def
          by (simp add: e_assms(2))
        obtain r where  \<mu>r: "\<mu> c s (tail G e) = ereal r"
           using e_assms(3) Suc(5) ds False
           by (cases "\<mu> c s (tail G e)", auto)
        obtain p where 
          "awalk s p (tail G e)" and
          \<mu>s: "\<mu> c s (tail G e) = ereal (awalk_cost c p)"
          using witness_path[OF \<mu>r] unfolding apath_def 
          by blast
        then have pe: "awalk s (p @ [e]) v" 
          using e_assms(1,2) by (auto simp: awalk_simps)
        hence muc:"\<mu> c s v \<le> \<mu> c s (tail G e) + ereal (c e)" 
        using \<mu>s min_cost_le_walk_cost[OF pe] by simp 
        thus  "dist v \<ge> \<mu> c s v"  using dmuc by simp
      qed simp
    qed (simp add: Suc(6,7))
  qed
qed

lemma (in shortest_path_pos_cost) tail_value_check: 
  fixes u :: 'a
  assumes "s \<in> verts G"
  shows "\<mu> c s s = ereal 0"
proof -
  have *: "awalk s [] s" using assms unfolding awalk_def by simp
  hence "\<mu> c s s \<le> ereal 0" using min_cost_le_walk_cost[OF *] by simp
  moreover
  have "(\<And>p. awalk s p s \<Longrightarrow> ereal(awalk_cost c p) \<ge> ereal 0)"
   using pos_cost pos_cost_pos_awalk_cost by auto
  hence "\<mu> c s s \<ge> ereal 0" 
    unfolding \<mu>_def by (blast intro: INF_greatest)
  ultimately
  show ?thesis by simp
qed

lemma (in shortest_path_pos_cost) num_not0:
  fixes v :: 'a
  assumes "v \<in> verts G"
  assumes "v \<noteq> s"
  assumes "num v \<noteq> \<infinity>"
  shows "num v \<noteq> enat 0"
proof -
  obtain ku where "num v = ku + enat 1" 
    using assms just by blast
  thus ?thesis  by (induct ku) auto
qed

lemma (in shortest_path_pos_cost) dist_ne_ninf:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "dist v \<noteq> -\<infinity>"
proof (cases "num v = \<infinity>")
case False 
  obtain n where "enat n = num v"
    using False by force
  thus ?thesis using assms False
  proof(induct n arbitrary: v) 
  case 0 thus ?case 
    using num_not0 tail_val by (cases "v=s", auto) 
  next
  case (Suc n)
    thus ?case 
    proof (cases "v=s") 
    case True 
      thus ?thesis using tail_val by simp
    next
    case False
      obtain e where e_assms:
        "e \<in> arcs G"
        "dist v = dist (tail G e) + ereal (c e)" 
        "num v = num (tail G e) + enat 1" 
        using just[OF Suc(3) False Suc(4)] by blast
      then have nsinf:"num (tail G e) \<noteq> \<infinity>" 
        by (metis Suc(2) enat.simps(3) enat_1 plus_enat_simps(2))
      then have ns:"enat n = num (tail G e)" 
        using e_assms(3) Suc(2) by force
      have "dist (tail G e ) \<noteq> - \<infinity>" 
        by (rule Suc(1) [OF ns tail_in_verts[OF e_assms(1)] nsinf])
      thus ?thesis using e_assms(2) by simp
    qed
  qed
next
case True 
  thus ?thesis using no_path[OF assms] by simp
qed

theorem (in shortest_path_pos_cost) correct_shortest_path:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "dist v = \<mu> c s v"
  using no_path[OF assms(1)] dist_le_\<mu>[OF assms(1)]
    dist_ge_\<mu>[OF assms(1) _ dist_ne_ninf[OF assms(1)] 
    tail_value_check[OF s_in_G] tail_val num_not0] 
    by fastforce

corollary (in shortest_path_pos_cost_pred) correct_shortest_path_pred:
  fixes v :: 'a
  assumes "v \<in> verts G"
  shows "dist v = \<mu> c s v"
  using correct_shortest_path assms by simp

end
