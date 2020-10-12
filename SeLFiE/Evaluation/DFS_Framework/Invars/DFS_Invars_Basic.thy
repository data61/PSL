section \<open>Basic Invariant Library\<close>
theory DFS_Invars_Basic
imports "../Param_DFS"
begin

text \<open>We provide more basic invariants of the DFS algorithm\<close>



subsection \<open>Basic Timing Invariants\<close>

(* Timing *)
abbreviation "the_discovered s v \<equiv> the (discovered s v)"
abbreviation "the_finished s v \<equiv> the (finished s v)"

locale timing_syntax
begin
  (* Timing related syntax shortcuts *) 
  notation the_discovered ("\<delta>")
  notation the_finished ("\<phi>")
end

context param_DFS begin context begin interpretation timing_syntax .

  definition "timing_common_inv s \<equiv> 
  \<comment> \<open>\<open>\<delta> s v < \<phi> s v\<close>\<close>
   (\<forall>v \<in> dom (finished s). \<delta> s v < \<phi> s v)

  \<comment> \<open>\<open>v \<noteq> w \<longrightarrow> \<delta> s v \<noteq> \<delta> s w \<and> \<phi> s v \<noteq> \<phi> s w\<close>\<close>
  \<comment> \<open>Can't use \<open>card dom = card ran\<close> as the maps may be infinite ...\<close>
  \<and> (\<forall>v \<in> dom (discovered s). \<forall>w \<in> dom (discovered s). v \<noteq> w \<longrightarrow> \<delta> s v \<noteq> \<delta> s w)
  \<and> (\<forall>v \<in> dom (finished s). \<forall>w \<in> dom (finished s). v \<noteq> w \<longrightarrow> \<phi> s v \<noteq> \<phi> s w)

  \<comment> \<open>\<open>\<delta> s v < counter \<and> \<phi> s v < counter\<close>\<close>
  \<and> (\<forall>v \<in> dom (discovered s). \<delta> s v < counter s)
  \<and> (\<forall>v \<in> dom (finished s). \<phi> s v < counter s)

  \<and> (\<forall>v \<in> dom (finished s). \<forall>w \<in> succ v. \<delta> s w < \<phi> s v)"

  lemma timing_common_inv: 
    "is_invar timing_common_inv"
  proof (induction rule: is_invarI)
    case (finish s s') then interpret DFS_invar where s=s by simp

    from finish have NE: "stack s \<noteq> []" by (simp add: cond_alt)
    
    have *: "hd (stack s) \<notin> dom (finished s)" "hd (stack s) \<in> dom (discovered s)"
      using stack_not_finished stack_discovered hd_in_set[OF NE]
      by blast+

    from discovered_closed have 
      "(E - pending s) `` {hd (stack s)} \<subseteq> dom (discovered s)"
      using hd_in_set[OF NE]
      by (auto simp add: discovered_closed_def)
    hence succ_hd: "pending s `` {hd (stack s)} = {} 
      \<Longrightarrow> succ (hd (stack s)) \<subseteq> dom (discovered s)"
      by blast
    
    from finish show ?case 
        apply (simp add: timing_common_inv_def)
        apply (intro conjI)
        using * apply simp
        using * apply simp
        apply (metis less_irrefl)
        apply (metis less_irrefl)
        apply (metis less_SucI)
        apply (metis less_SucI)
        apply (blast dest!: succ_hd)
        using * apply simp
        done
  next
    case (discover s) then interpret DFS_invar where s=s by simp
    from discover show ?case
      apply (simp add: timing_common_inv_def)
      apply (intro conjI)
      using finished_discovered apply fastforce
      apply (metis less_irrefl)
      apply (metis less_irrefl)
      apply (metis less_SucI)
      apply (metis less_SucI)
      using finished_imp_succ_discovered apply fastforce
      done
  next
    case (new_root s s' v0) then interpret DFS_invar where s=s by simp
    from new_root show ?case
      apply (simp add: timing_common_inv_def)
      apply (intro conjI)
      using finished_discovered apply fastforce
      apply (metis less_irrefl)
      apply (metis less_irrefl)
      apply (metis less_SucI)
      apply (metis less_SucI)
      using finished_imp_succ_discovered apply fastforce
      done
  qed (simp_all add: timing_common_inv_def)
end end

context DFS_invar begin context begin interpretation timing_syntax .

  lemmas s_timing_common_inv = 
    timing_common_inv[THEN make_invar_thm]

  lemma timing_less_counter:
    "v \<in> dom (discovered s) \<Longrightarrow> \<delta> s v < counter s"
    "v \<in> dom (finished s) \<Longrightarrow> \<phi> s v < counter s"
    using s_timing_common_inv
    by (auto simp add: timing_common_inv_def)

  lemma disc_lt_fin:
    "v \<in> dom (finished s) \<Longrightarrow> \<delta> s v < \<phi> s v"
    using s_timing_common_inv
    by (auto simp add: timing_common_inv_def)

  lemma disc_unequal:
    assumes "v \<in> dom (discovered s)" "w \<in> dom (discovered s)"
    and "v \<noteq> w"
    shows "\<delta> s v \<noteq> \<delta> s w"
    using s_timing_common_inv assms
    by (auto simp add: timing_common_inv_def)

  lemma fin_unequal:
    assumes "v \<in> dom (finished s)" "w \<in> dom (finished s)"
    and "v \<noteq> w"
    shows "\<phi> s v \<noteq> \<phi> s w"
    using s_timing_common_inv assms
    by (auto simp add: timing_common_inv_def)

  lemma finished_succ_fin:
    assumes "v \<in> dom (finished s)"
    and "w \<in> succ v"
    shows "\<delta> s w < \<phi> s v"
    using assms s_timing_common_inv
    by (simp add: timing_common_inv_def)
end end

context param_DFS begin context begin interpretation timing_syntax .

  lemma i_prev_stack_discover_all:
    "is_invar (\<lambda>s. \<forall> n < length (stack s). \<forall> v \<in> set (drop (Suc n) (stack s)). 
                   \<delta> s (stack s ! n) > \<delta> s v)"
  proof (induct rule: is_invarI)
    case (finish s) thus ?case 
      by (cases "stack s") auto
  next
    case (discover s s' u v) 
    hence EQ[simp]: "discovered s' = (discovered s)(v \<mapsto> counter s)"
                    "stack s' = v#stack s"
      by simp_all
    
    from discover interpret DFS_invar where s=s by simp
    from discover stack_discovered have v_ni: "v \<notin> set (stack s)" by auto

    from stack_discovered timing_less_counter have 
      "\<And>w. w \<in> set (stack s) \<Longrightarrow> \<delta> s w < counter s" 
      by blast
    with v_ni have "\<And>w. w \<in> set (stack s) \<Longrightarrow> \<delta> s' w < \<delta> s' v" by auto
    hence "\<And>w. w \<in> set (drop (Suc 0) (stack s')) \<Longrightarrow> \<delta> s' w < \<delta> s' (stack s' ! 0)" 
      by auto
      
    moreover
    from v_ni have 
      "\<And>n. \<lbrakk>n < (length (stack s')); n > 0\<rbrakk>
      \<Longrightarrow> \<delta> s' (stack s' ! n) = \<delta> s (stack s' ! n)" 
      by auto
    with discover(1) v_ni 
    have  "\<And>n. \<lbrakk>n < (length (stack s')) - 1; n > 0\<rbrakk> 
      \<Longrightarrow> \<forall> w \<in> set (drop (Suc n) (stack s')). \<delta> s' (stack s' ! n) > \<delta> s' w"
      by (auto dest: in_set_dropD)
    ultimately show ?case 
      by (metis drop_Suc_Cons length_drop length_pos_if_in_set length_tl 
        list.sel(3) neq0_conv nth_Cons_0 EQ(2) zero_less_diff)
  qed simp_all
end end

context DFS_invar begin context begin interpretation timing_syntax .

  lemmas prev_stack_discover_all 
    = i_prev_stack_discover_all[THEN make_invar_thm]

  lemma prev_stack_discover:
    "\<lbrakk>n < length (stack s); v \<in> set (drop (Suc n) (stack s)) \<rbrakk>
     \<Longrightarrow> \<delta> s (stack s ! n) > \<delta> s v"
    by (metis prev_stack_discover_all)

  lemma Suc_stack_discover:
    assumes n: "n < (length (stack s)) - 1"
    shows "\<delta> s (stack s ! n) > \<delta> s (stack s ! Suc n)"
  proof -
    from prev_stack_discover assms have 
      "\<And> v. v \<in> set (drop (Suc n) (stack s)) \<Longrightarrow> \<delta> s (stack s ! n) > \<delta> s v" 
      by fastforce
    moreover from n have "stack s ! Suc n \<in> set (drop (Suc n) (stack s))" 
      using in_set_conv_nth by fastforce
    ultimately show ?thesis .
  qed

  lemma tl_lt_stack_hd_discover:
    assumes notempty: "stack s \<noteq> []"
    and "x \<in> set (tl (stack s))"
    shows "\<delta> s x < \<delta> s (hd (stack s))"
  proof -
    from notempty obtain y ys where "stack s = y#ys" by (metis list.exhaust)
    with assms show ?thesis
      using prev_stack_discover
      by (cases ys) force+
  qed

  lemma stack_nth_order:
    assumes l: "i < length (stack s)" "j < length (stack s)"
    shows "\<delta> s (stack s ! i) < \<delta> s (stack s ! j) \<longleftrightarrow> i > j" (is "\<delta> s ?i < \<delta> s ?j \<longleftrightarrow> _")
  proof
    assume \<delta>: "\<delta> s ?i < \<delta> s ?j"
    
    from l stack_set_def have 
      disc: "?i \<in> dom (discovered s)" "?j \<in> dom (discovered s)"
      by auto
    with disc_unequal[OF disc] \<delta> have "i \<noteq> j" by auto

    moreover
    {
      assume "i < j"

      with l have "stack s ! j \<in> set (drop (Suc i) (stack s))" 
        using in_set_drop_conv_nth[of "stack s ! j" "Suc i" "stack s"]
        by fastforce
      with prev_stack_discover l have "\<delta> s (stack s ! j) < \<delta> s (stack s ! i)" 
        by simp
      with \<delta> have "False" by simp
    }
    ultimately show "i > j" by force
  next
    assume "i > j"
    with l have "stack s ! i \<in> set (drop (Suc j) (stack s))" 
      using in_set_drop_conv_nth[of "stack s ! i" "Suc j" "stack s"]
      by fastforce
    with prev_stack_discover l show "\<delta> s ?i < \<delta> s ?j" by simp
  qed
end end

subsection \<open>Paranthesis Theorem\<close>
(* Parenthesis Thm *)
context param_DFS begin context begin interpretation timing_syntax .

  definition "parenthesis s \<equiv>
    \<forall>v \<in> dom (discovered s). \<forall>w \<in> dom (discovered s).
     \<delta> s v < \<delta> s w \<and> v \<in> dom (finished s) \<longrightarrow> (
             \<phi> s v < \<delta> s w \<comment> \<open>disjoint\<close>
           \<or> (\<phi> s v > \<delta> s w \<and> w \<in> dom (finished s) \<and> \<phi> s w < \<phi> s v))"

  lemma i_parenthesis: "is_invar parenthesis"
  proof (induct rule: is_invarI)
    case (finish s s')
    hence EQ[simp]: "discovered s' = discovered s" 
                    "counter s' = Suc (counter s)"
                    "finished s' = finished s(hd (stack s) \<mapsto> counter s)"
      by simp_all

    from finish interpret DFS_invar where s=s by simp
    from finish have NE[simp]: "stack s \<noteq> []" by (simp add: cond_alt)

    {
      fix x y
      assume  dom: "x \<in> dom (discovered s')" "y \<in> dom (discovered s')"
        and \<delta>: "\<delta> s' x < \<delta> s' y"
        and f: "x \<in> dom (finished s')"
      hence neq: "x \<noteq> y" by force

      note assms = dom \<delta> f EQ

      let ?DISJ = "\<phi> s' x < \<delta> s' y"
      let ?IN = "\<delta> s' y < \<phi> s' x \<and> y \<in> dom (finished s') \<and> \<phi> s' y < \<phi> s' x"

      have "?DISJ \<or> ?IN"
      proof (cases "x = hd (stack s)")
        case True note x_is_hd = this
        hence \<phi>x: "\<phi> s' x = counter s" by simp
        from x_is_hd neq have y_not_hd: "y \<noteq> hd (stack s)" by simp
        
        have "\<delta> s y < \<phi> s' x \<and> y \<in> dom (finished s) \<and> \<phi> s y < \<phi> s' x"
        proof (cases "y \<in> set (stack s)")
          \<comment> \<open>y on stack is not possible: According to @{thm [display] \<delta>} it is discovered after @{text "x (= hd (stack s))"}\<close>
          case True with y_not_hd have "y \<in> set (tl (stack s))" 
            by (cases "stack s") simp_all
          with tl_lt_stack_hd_discover[OF NE] \<delta> x_is_hd have "\<delta> s y < \<delta> s x" 
            by simp
          with \<delta> have False by simp
          thus ?thesis ..
        next
          case False \<comment> \<open>y must be a successor of @{text "x (= (hd (stack s)))"}\<close>
          from dom have "y \<in> dom (discovered s)" by simp
          with False discovered_not_stack_imp_finished  have *: 
            "y \<in> dom (finished s)" 
            by simp
          moreover with timing_less_counter \<phi>x have "\<phi> s y < \<phi> s' x" by simp
          moreover with * disc_lt_fin \<phi>x have "\<delta> s y < \<phi> s' x" 
            by (metis less_trans)
          ultimately show ?thesis by simp
        qed
        with y_not_hd show ?thesis by simp
      next
        case False note [simp] = this
        show ?thesis
        proof (cases "y = hd (stack s)")
          case False with finish assms show ?thesis 
            by (simp add: parenthesis_def)
        next
          case True with stack_not_finished have "y \<notin> dom (finished s)" 
            using hd_in_set[OF NE] 
            by auto
          with finish assms have "\<phi> s x < \<delta> s y" 
            unfolding parenthesis_def
            by auto
          hence ?DISJ by simp
          thus ?thesis ..
        qed
      qed
    }
    thus ?case by (simp add: parenthesis_def)
  next
    case (discover s s' u v)
    hence EQ[simp]: "discovered s' = (discovered s)(v \<mapsto> counter s)" 
                    "finished s' = finished s"
                    "counter s' = Suc (counter s)"
      by simp_all
    
    from discover interpret DFS_invar where s=s by simp
    from discover finished_discovered have 
      V': "v \<notin> dom (discovered s)" "v \<notin> dom (finished s)" 
      by auto

    {
      fix x y
      assume  dom: "x \<in> dom (discovered s')" "y \<in> dom (discovered s')"
        and \<delta>: "\<delta> s' x < \<delta> s' y"
        and f: "x \<in> dom (finished s')"

      let ?DISJ = "\<phi> s' x < \<delta> s' y"
      let ?IN = "\<delta> s' y < \<phi> s' x \<and> y \<in> dom (finished s') \<and> \<phi> s' y < \<phi> s' x"
      
      from dom V' f have x: "x \<in> dom (discovered s)""x \<noteq> v" by auto
      
      have "?DISJ \<or> ?IN"
      proof (cases "y = v")
        case True hence "\<delta> s' y = counter s" by simp
        moreover from timing_less_counter x f have "\<phi> s' x < counter s" by auto
        ultimately have "?DISJ" by simp
        thus ?thesis ..
      next
        case False with dom have "y \<in> dom (discovered s)" by simp
        with discover False \<delta> f x show ?thesis by (simp add: parenthesis_def)
      qed
    }
    thus ?case by (simp add: parenthesis_def)
  next
    case (new_root s s' v0) 
    then interpret DFS_invar where s=s by simp
    
    from finished_discovered new_root have "v0 \<notin> dom (finished s')" by auto
    with new_root timing_less_counter show ?case by (simp add: parenthesis_def)
  qed (simp_all add: parenthesis_def)
end end

context DFS_invar begin context begin interpretation timing_syntax .

  lemma parenthesis:
    assumes "v \<in> dom (finished s)" "w \<in> dom (discovered s)"
    and "\<delta> s v < \<delta> s w"
    shows "\<phi> s v < \<delta> s w \<comment> \<open>disjoint\<close>
           \<or> (\<phi> s v > \<delta> s w \<and> w \<in> dom (finished s) \<and> \<phi> s w < \<phi> s v)"
    using assms
    using i_parenthesis[THEN make_invar_thm]
    using finished_discovered
    unfolding parenthesis_def
    by blast

  lemma parenthesis_contained:
    assumes "v \<in> dom (finished s)" "w \<in> dom (discovered s)"
    and "\<delta> s v < \<delta> s w" "\<phi> s v > \<delta> s w"
    shows "w \<in> dom (finished s) \<and> \<phi> s w < \<phi> s v"
    using parenthesis assms
    by force
  
  lemma parenthesis_disjoint:
    assumes "v \<in> dom (finished s)" "w \<in> dom (discovered s)"
    and "\<delta> s v < \<delta> s w" "\<phi> s w > \<phi> s v"
    shows "\<phi> s v < \<delta> s w"
    using parenthesis assms
    by force

  lemma finished_succ_contained:
    assumes "v \<in> dom (finished s)"
    and "w \<in> succ v"
    and "\<delta> s v < \<delta> s w"
    shows "w \<in> dom (finished s) \<and> \<phi> s w < \<phi> s v"
    using finished_succ_fin finished_imp_succ_discovered parenthesis_contained
    using assms
    by metis

end end


subsection \<open>Edge Types\<close>
context param_DFS 
begin
  abbreviation "edges s \<equiv> tree_edges s \<union> cross_edges s \<union> back_edges s"

  (* Demo for simple invariant proof *)
  lemma "is_invar (\<lambda>s. finite (edges s))"
    by (induction rule: establish_invarI) auto

  text \<open>Sometimes it's useful to just chose between tree-edges and non-tree.\<close>
  lemma edgesE_CB:
    assumes "x \<in> edges s"
    and "x \<in> tree_edges s \<Longrightarrow> P"
    and "x \<in> cross_edges s \<union> back_edges s \<Longrightarrow> P"
    shows "P"
    using assms by auto

  definition "edges_basic s \<equiv> 
     Field (back_edges s) \<subseteq> dom (discovered s) \<and> back_edges s \<subseteq> E - pending s
   \<and> Field (cross_edges s) \<subseteq> dom (discovered s) \<and> cross_edges s \<subseteq> E - pending s
   \<and> Field (tree_edges s) \<subseteq> dom (discovered s) \<and> tree_edges s \<subseteq> E - pending s
   \<and> back_edges s \<inter> cross_edges s = {}
   \<and> back_edges s \<inter> tree_edges s = {}
   \<and> cross_edges s \<inter> tree_edges s = {}
   "

  lemma i_edges_basic:
    "is_invar edges_basic"
    unfolding edges_basic_def[abs_def]
  proof (induct rule: is_invarI_full)
    case (back_edge s)
    then interpret DFS_invar where s=s by simp
    from back_edge show ?case by (auto dest: pendingD)
  next
    case (cross_edge s)
    then interpret DFS_invar where s=s by simp
    from cross_edge show ?case by (auto dest: pendingD)
  next
    case (discover s)
    then interpret DFS_invar where s=s by simp
    from discover show ?case 
      (* Speed optimized proof, using only auto takes too long *)
      apply (simp add: Field_def Range_def Domain_def)
      apply (drule pendingD) apply simp
      by (blast)
  next
    case (new_root s) 
    thus ?case by (simp add: Field_def) blast
  qed auto

  lemmas (in DFS_invar) edges_basic = i_edges_basic[THEN make_invar_thm]
    
  lemma i_edges_covered: 
    "is_invar (\<lambda>s. (E \<inter> dom (discovered s) \<times> UNIV) - pending s = edges s)"
  proof (induction rule: is_invarI_full)
    case (new_root s s' v0) 
    interpret DFS_invar G param s by fact  

    from new_root empty_stack_imp_empty_pending 
    have [simp]: "pending s = {}" by simp

    from \<open>v0 \<notin> dom (discovered s)\<close> 
    have [simp]: "E \<inter> insert v0 (dom (discovered s)) \<times> UNIV - {v0} \<times> succ v0 
      = E \<inter> dom (discovered s) \<times> UNIV" by auto

    from new_root show ?case by simp
  next
    case (cross_edge s s' u v) 
    interpret DFS_invar G param s by fact  

    from cross_edge stack_discovered have "u \<in> dom (discovered s)" 
      by (cases "stack s") auto

    with cross_edge(2-) pending_ssE have 
      "E \<inter> dom (discovered s) \<times> UNIV - (pending s - {(hd (stack s), v)})
      = insert (hd (stack s), v) (E \<inter> dom (discovered s) \<times> UNIV - pending s)"
      by auto

    thus ?case using cross_edge by simp
  next
    case (back_edge s s' u v)
    interpret DFS_invar G param s by fact  

    from back_edge stack_discovered have "u \<in> dom (discovered s)" 
      by (cases "stack s") auto

    with back_edge(2-) pending_ssE have 
      "E \<inter> dom (discovered s) \<times> UNIV - (pending s - {(hd (stack s), v)})
      = insert (hd (stack s), v) (E \<inter> dom (discovered s) \<times> UNIV - pending s)"
      by auto

    thus ?case using back_edge by simp
  next
    case (discover s s' u v)
    interpret DFS_invar G param s by fact  

    from discover stack_discovered have "u \<in> dom (discovered s)" 
      by (cases "stack s") auto

    with discover(2-) pending_ssE have 
      "E \<inter> insert v (dom (discovered s)) \<times> UNIV 
        - (pending s - {(hd (stack s), v)} \<union> {v} \<times> succ v)
      = insert (hd (stack s), v) (E \<inter> dom (discovered s) \<times> UNIV - pending s)"
      by auto

    thus ?case using discover by simp
  qed simp_all
end

context DFS_invar begin

  lemmas edges_covered = 
    i_edges_covered[THEN make_invar_thm]

  lemma edges_ss_reachable_edges:
    "edges s \<subseteq> E \<inter> reachable \<times> UNIV"
    using edges_covered discovered_reachable
    by (fast intro: rtrancl_image_advance_rtrancl)

  lemma nc_edges_covered:
    assumes "\<not>cond s" "\<not>is_break param s"
    shows "E \<inter> reachable \<times> UNIV = edges s"
  proof -
    from assms have [simp]: "stack s = []" 
      unfolding cond_def by (auto simp: pred_defs)
    hence [simp]: "pending s = {}" by (rule empty_stack_imp_empty_pending)
    
    
    from edges_covered nc_discovered_eq_reachable[OF assms] 
    show ?thesis by simp
  qed

  lemma 
    tree_edges_ssE: "tree_edges s \<subseteq> E" and
    tree_edges_not_pending: "tree_edges s \<subseteq> - pending s" and
    tree_edge_is_succ: "(v,w) \<in> tree_edges s \<Longrightarrow> w \<in> succ v" and
    tree_edges_discovered: "Field (tree_edges s) \<subseteq> dom (discovered s)" and

    cross_edges_ssE: "cross_edges s \<subseteq> E" and
    cross_edges_not_pending: "cross_edges s \<subseteq> - pending s" and
    cross_edge_is_succ: "(v,w) \<in> cross_edges s \<Longrightarrow> w \<in> succ v" and
    cross_edges_discovered: "Field (cross_edges s) \<subseteq> dom (discovered s)" and

    back_edges_ssE: "back_edges s \<subseteq> E" and
    back_edges_not_pending: "back_edges s \<subseteq> - pending s" and
    back_edge_is_succ: "(v,w) \<in> back_edges s \<Longrightarrow> w \<in> succ v" and
    back_edges_discovered: "Field (back_edges s) \<subseteq> dom (discovered s)"
    using edges_basic
    unfolding edges_basic_def 
    by auto

  lemma edges_disjoint: 
   "back_edges s \<inter> cross_edges s = {}"
   "back_edges s \<inter> tree_edges s = {}"
   "cross_edges s \<inter> tree_edges s = {}"
    using edges_basic
    unfolding edges_basic_def 
    by auto

  lemma tree_edge_imp_discovered:
    "(v,w) \<in> tree_edges s \<Longrightarrow> v \<in> dom (discovered s)"
    "(v,w) \<in> tree_edges s \<Longrightarrow> w \<in> dom (discovered s)"
    using tree_edges_discovered
    by (auto simp add: Field_def)

  lemma back_edge_imp_discovered:
    "(v,w) \<in> back_edges s \<Longrightarrow> v \<in> dom (discovered s)"
    "(v,w) \<in> back_edges s \<Longrightarrow> w \<in> dom (discovered s)"
    using back_edges_discovered
    by (auto simp add: Field_def)

  lemma cross_edge_imp_discovered:
    "(v,w) \<in> cross_edges s \<Longrightarrow> v \<in> dom (discovered s)"
    "(v,w) \<in> cross_edges s \<Longrightarrow> w \<in> dom (discovered s)"
    using cross_edges_discovered
    by (auto simp add: Field_def)

  lemma edge_imp_discovered:
    "(v,w) \<in> edges s \<Longrightarrow> v \<in> dom (discovered s)"
    "(v,w) \<in> edges s \<Longrightarrow> w \<in> dom (discovered s)"
    using tree_edge_imp_discovered cross_edge_imp_discovered back_edge_imp_discovered
    by blast+

  lemma tree_edges_finite[simp, intro!]: "finite (tree_edges s)"
    using finite_subset[OF tree_edges_discovered discovered_finite] by simp

  lemma cross_edges_finite[simp, intro!]: "finite (cross_edges s)"
    using finite_subset[OF cross_edges_discovered discovered_finite] by simp

  lemma back_edges_finite[simp, intro!]: "finite (back_edges s)"
    using finite_subset[OF back_edges_discovered discovered_finite] by simp

  lemma edges_finite: "finite (edges s)"
    by auto

  
end

subsubsection \<open>Properties of the DFS Tree\<close>
(* Tree *)

context DFS_invar begin context begin interpretation timing_syntax .
  lemma tree_edge_disc_lt_fin:
    "(v,w) \<in> tree_edges s \<Longrightarrow> v \<in> dom (finished s) \<Longrightarrow> \<delta> s w < \<phi> s v"
    by (metis finished_succ_fin tree_edge_is_succ)

  lemma back_edge_disc_lt_fin:
    "(v,w) \<in> back_edges s \<Longrightarrow> v \<in> dom (finished s) \<Longrightarrow> \<delta> s w < \<phi> s v"
    by (metis finished_succ_fin back_edge_is_succ)

  lemma cross_edge_disc_lt_fin:
    "(v,w) \<in> cross_edges s \<Longrightarrow> v \<in> dom (finished s) \<Longrightarrow> \<delta> s w < \<phi> s v"
    by (metis finished_succ_fin cross_edge_is_succ)
end end

(* Stack & Tree *)
context param_DFS begin

  lemma i_stack_is_tree_path:
    "is_invar (\<lambda>s. stack s \<noteq> [] \<longrightarrow> (\<exists>v0 \<in> V0. 
        path (tree_edges s) v0 (rev (tl (stack s))) (hd (stack s))))"
  proof (induct rule: is_invarI)
    case (discover s s' u v)
    hence EQ[simp]: "stack s' = v # stack s"
                    "tree_edges s' = insert (hd (stack s), v) (tree_edges s)"
      by simp_all
    from discover have NE[simp]: "stack s \<noteq> []" by simp

    from discover obtain v0 where 
      "v0 \<in> V0"
      "path (tree_edges s) v0 (rev (tl (stack s))) (hd (stack s))"
      by blast
    with path_mono[OF _ this(2)] EQ have 
      "path (tree_edges s') v0 (rev (tl (stack s))) (hd (stack s))" 
      by blast
    with \<open>v0 \<in> V0\<close> show ?case
      by (cases "stack s") (auto simp: path_simps)

  next
    case (finish s s')
    hence EQ[simp]: "stack s' = tl (stack s)"
                    "tree_edges s' = tree_edges s"
      by simp_all

    from finish obtain v0 where
      "v0 \<in> V0"
      "path (tree_edges s) v0 (rev (tl (stack s))) (hd (stack s))"
      by blast
    hence P: "path (tree_edges s') v0 (rev (stack s')) (hd (stack s))" by simp
      
    show ?case
    proof
      assume A: "stack s' \<noteq> []"
      with P have "(hd (stack s'), hd (stack s)) \<in> tree_edges s'"
        by (auto simp: neq_Nil_conv path_simps)
      moreover from P A have 
        "path (tree_edges s') v0 (rev (tl (stack s')) @ [hd (stack s')]) (hd (stack s))"
        by (simp)
      moreover note \<open>v0 \<in> V0\<close>
      ultimately show "\<exists>v0\<in>V0. path (tree_edges s') v0 (rev (tl (stack s'))) (hd (stack s'))"
        by (auto simp add: path_append_conv)
    qed
  qed simp_all
end

context DFS_invar begin

  lemmas stack_is_tree_path = 
    i_stack_is_tree_path[THEN make_invar_thm, rule_format]

  lemma stack_is_path:
    "stack s \<noteq> [] \<Longrightarrow> \<exists>v0\<in>V0. path E v0 (rev (tl (stack s))) (hd (stack s))"
    using stack_is_tree_path path_mono[OF tree_edges_ssE]
    by blast

  lemma hd_succ_stack_is_path:
    assumes ne: "stack s \<noteq> []"
    and succ: "v \<in> succ (hd (stack s))"
    shows "\<exists>v0\<in>V0. path E v0 (rev (stack s)) v"
  proof -
    from stack_is_path[OF ne] succ obtain v0 where
      "v0 \<in> V0"
      "path E v0 (rev (tl (stack s)) @ [hd (stack s)]) v"
      by (auto simp add: path_append_conv)
    thus ?thesis using ne
      by (cases "stack s") auto
  qed

  lemma tl_stack_hd_tree_path:
    assumes "stack s \<noteq> []"
    and "v \<in> set (tl (stack s))"
    shows "(v, hd (stack s)) \<in> (tree_edges s)\<^sup>+"
  proof -
    from stack_is_tree_path assms obtain v0 where 
      "path (tree_edges s) v0 (rev (tl (stack s))) (hd (stack s))" 
      by auto
    from assms path_member_reach_end[OF this] show ?thesis by simp
  qed
end

context param_DFS begin
  definition "tree_discovered_inv s \<equiv>
                       (tree_edges s = {} \<longrightarrow> dom (discovered s) \<subseteq> V0 \<and> (stack s = [] \<or> (\<exists>v0\<in>V0. stack s = [v0])))
                     \<and> (tree_edges s \<noteq> {} \<longrightarrow> (tree_edges s)\<^sup>+ `` V0 \<union> V0 = dom (discovered s) \<union> V0)"


  lemma i_tree_discovered_inv: 
    "is_invar tree_discovered_inv"
  proof (induct rule: is_invarI)
    case (discover s s' u v) 
    hence EQ[simp]: "stack s' = v # stack s"
                    "tree_edges s' = insert (hd (stack s), v) (tree_edges s)"
                    "discovered s' = (discovered s)(v \<mapsto> counter s)"
      by simp_all
    
    from discover interpret DFS_invar where s=s by simp

    from discover have NE[simp]: "stack s \<noteq> []" by simp
    note TDI = \<open>tree_discovered_inv s\<close>[unfolded tree_discovered_inv_def]

    have "tree_edges s' = {} \<longrightarrow> dom (discovered s') \<subseteq> V0 \<and> (stack s' = [] \<or> (\<exists>v0\<in>V0. stack s' = [v0]))"
      by simp \<comment> \<open>@{text "tree_edges s' \<noteq> {}"}\<close>

    moreover {
      fix x
      assume A: "x \<in> (tree_edges s')\<^sup>+ `` V0 \<union> V0" "x \<notin> V0"
      then obtain y where y: "(y,x) \<in> (tree_edges s')\<^sup>+" "y \<in> V0" by auto
     

      have "x \<in> dom (discovered s') \<union> V0"
      proof (cases "tree_edges s = {}")
        case True with discover A have "(tree_edges s')\<^sup>+ = {(hd (stack s), v)}"
          by (simp add: trancl_single)
        with A show ?thesis by auto
      next
        case False note t_ne = this

        show ?thesis
        proof (cases "x = v")
          case True thus ?thesis by simp
        next
          case False with y have "(y,x) \<in> (tree_edges s)\<^sup>+"
          proof (induct rule: trancl_induct)
            case (step a b) hence "(a,b) \<in> tree_edges s" by simp
            with tree_edge_imp_discovered have "a \<in> dom (discovered s)" by simp
            with discover have "a \<noteq> v" by blast
            with step show ?case by auto
          qed simp
          with \<open>y \<in> V0\<close> have "x \<in> (tree_edges s)\<^sup>+ `` V0" by auto
          with t_ne TDI show ?thesis by auto
        qed
      qed
    } note t_d = this

    {
      fix x
      assume "x \<in> dom (discovered s') \<union> V0" "x \<notin> V0"
      hence A: "x \<in> dom (discovered s')" by simp

      have "x \<in> (tree_edges s')\<^sup>+ `` V0 \<union> V0"
      proof (cases "tree_edges s = {}")
        case True with trancl_single have "(tree_edges s')\<^sup>+ = {(hd (stack s), v)}" by simp
        moreover from True TDI have "hd (stack s) \<in> V0" "dom (discovered s) \<subseteq> V0" by auto
        ultimately show ?thesis using A \<open>x\<notin>V0\<close> by auto
      next
        case False note t_ne = this

        show ?thesis
        proof (cases "x=v")
          case False with A have "x \<in> dom (discovered s)" by simp
          with TDI t_ne \<open>x \<notin> V0\<close> have "x \<in> (tree_edges s)\<^sup>+ `` V0" by auto
          with trancl_sub_insert_trancl show ?thesis by simp blast
        next
          case True
          from t_ne TDI have "dom (discovered s) \<union> V0 = (tree_edges s)\<^sup>+ `` V0 \<union> V0"
            by simp

          moreover from stack_is_tree_path[OF NE] obtain v0 where "v0 \<in> V0" and 
            "(v0, hd (stack s)) \<in> (tree_edges s)\<^sup>*"
            by (blast intro!: path_is_rtrancl)
          with EQ have "(v0, hd (stack s)) \<in> (tree_edges s')\<^sup>*" by (auto intro: rtrancl_mono_mp)
          ultimately show ?thesis using \<open>v0 \<in> V0\<close> True by (auto elim: rtrancl_into_trancl1)
        qed
      qed
    } with t_d have "(tree_edges s')\<^sup>+ `` V0 \<union> V0 = dom (discovered s') \<union> V0" by blast

    ultimately show ?case by (simp add: tree_discovered_inv_def)
  qed (auto simp add: tree_discovered_inv_def)
      
  lemmas (in DFS_invar) tree_discovered_inv = 
    i_tree_discovered_inv[THEN make_invar_thm]

  lemma (in DFS_invar) discovered_iff_tree_path:
    "v \<notin> V0 \<Longrightarrow> v \<in> dom (discovered s) \<longleftrightarrow> (\<exists>v0\<in>V0. (v0,v) \<in> (tree_edges s)\<^sup>+)"
    using tree_discovered_inv
    by (auto simp add: tree_discovered_inv_def)

  lemma i_tree_one_predecessor:
    "is_invar (\<lambda>s. \<forall>(v,v') \<in> tree_edges s. \<forall>y. y \<noteq> v \<longrightarrow> (y,v') \<notin> tree_edges s)"
  proof (induct rule: is_invarI)
    case (discover s s' u v) 
    hence EQ[simp]: "tree_edges s' = insert (hd (stack s),v) (tree_edges s)" by simp

    from discover interpret DFS_invar where s=s by simp
    from discover have NE[simp]: "stack s \<noteq> []" by (simp add: cond_alt)

    {
      fix w w' y
      assume *: "(w,w') \<in> tree_edges s'"
        and  "y \<noteq> w"

      from discover stack_discovered have v_hd: "hd (stack s) \<noteq> v" 
        using hd_in_set[OF NE] by blast
      from discover tree_edges_discovered have 
        v_notin_tree: "\<forall>(x,x') \<in> tree_edges s. x \<noteq> v \<and> x' \<noteq> v" 
        by (blast intro!: Field_not_elem)

      have "(y,w') \<notin> tree_edges s'"
      proof (cases "w = hd (stack s)")
        case True
        have "(y,v) \<notin> tree_edges s'"
        proof (rule notI)
          assume "(y,v) \<in> tree_edges s'" 
          with True \<open>y\<noteq>w\<close> have "(y,v) \<in> tree_edges s" by simp
          with v_notin_tree show False by auto
        qed
        with True * \<open>y\<noteq>w\<close> v_hd show ?thesis 
          apply (cases "w = v")
          apply simp 
          using discover apply simp apply blast
          done
      next
        case False with v_notin_tree * \<open>y\<noteq>w\<close> v_hd 
        show ?thesis
          apply (cases "w' = v")
          apply simp apply blast
          using discover apply simp apply blast
          done
      qed
    }
    thus ?case by blast
  qed simp_all
 
  lemma (in DFS_invar) tree_one_predecessor:
    assumes "(v,w) \<in> tree_edges s"
    and "a \<noteq> v"
    shows "(a,w) \<notin> tree_edges s"
    using assms make_invar_thm[OF i_tree_one_predecessor]
    by blast

  lemma (in DFS_invar) tree_eq_rule:
    "\<lbrakk>(v,w) \<in> tree_edges s; (u,w) \<in> tree_edges s\<rbrakk> \<Longrightarrow> v=u"
    using tree_one_predecessor
    by blast

context begin interpretation timing_syntax .

  lemma i_tree_edge_disc:
    "is_invar (\<lambda>s. \<forall>(v,v') \<in> tree_edges s. \<delta> s v < \<delta> s v')"
  proof (induct rule: is_invarI)
    case (discover s s' u v) 
    hence EQ[simp]: "tree_edges s' = insert (hd (stack s), v) (tree_edges s)"
                    "discovered s' = (discovered s)(v \<mapsto> counter s)"
      by simp_all

    from discover interpret DFS_invar where s=s by simp
    from discover have NE[simp]: "stack s \<noteq> []" by (simp add: cond_alt)
    
    from discover tree_edges_discovered have 
      v_notin_tree: "\<forall>(x,x') \<in> tree_edges s. x \<noteq> v \<and> x' \<noteq> v" 
      by (blast intro!: Field_not_elem)
    from discover stack_discovered have 
      v_hd: "hd (stack s) \<noteq> v" 
      using hd_in_set[OF NE] 
      by blast
    
    {
      fix a b
      assume T: "(a,b) \<in> tree_edges s'"
      have "\<delta> s' a < \<delta> s' b"
      proof (cases "b = v")
        case True with T v_notin_tree have [simp]: "a = hd (stack s)" by auto
        with stack_discovered have "a \<in> dom (discovered s)" 
          by (metis hd_in_set NE subsetD)
        with v_hd True timing_less_counter show ?thesis by simp
      next
        case False with v_notin_tree T have "(a,b) \<in> tree_edges s" "a \<noteq> v" by auto
        with discover have "\<delta> s a < \<delta> s b" by auto
        with False \<open>a\<noteq>v\<close> show ?thesis by simp
      qed
    } thus ?case by blast
  next
    case (new_root s s' v0) then interpret DFS_invar where s=s by simp
    from new_root have "tree_edges s' = tree_edges s" by simp
    moreover from tree_edge_imp_discovered new_root have "\<forall>(v,v') \<in> tree_edges s. v \<noteq> v0 \<and> v' \<noteq> v0" by blast
    ultimately show ?case using new_root by auto
  qed simp_all
end end

context DFS_invar begin context begin interpretation timing_syntax .

  lemma tree_edge_disc:
    "(v,w) \<in> tree_edges s \<Longrightarrow> \<delta> s v < \<delta> s w"
    using i_tree_edge_disc[THEN make_invar_thm]
    by blast
  
  lemma tree_path_disc:
    "(v,w) \<in> (tree_edges s)\<^sup>+ \<Longrightarrow> \<delta> s v < \<delta> s w"
    by (auto elim!: trancl_induct dest: tree_edge_disc)

  lemma no_loop_in_tree:
    "(v,v) \<notin> (tree_edges s)\<^sup>+"
    using tree_path_disc by auto

  lemma tree_acyclic:
    "acyclic (tree_edges s)"
    by (metis acyclicI no_loop_in_tree)

  lemma no_self_loop_in_tree:
    "(v,v) \<notin> tree_edges s"
    using tree_edge_disc by auto

  lemma tree_edge_unequal:
    "(v,w) \<in> tree_edges s \<Longrightarrow> v \<noteq> w"
    by (metis no_self_loop_in_tree)

  lemma tree_path_unequal:
    "(v,w) \<in> (tree_edges s)\<^sup>+ \<Longrightarrow> v \<noteq> w"
    by (metis no_loop_in_tree)

  lemma tree_subpath':
    assumes x: "(x,v) \<in> (tree_edges s)\<^sup>+"
    and y: "(y,v) \<in> (tree_edges s)\<^sup>+"
    and "x \<noteq> y"
    shows "(x,y) \<in> (tree_edges s)\<^sup>+ \<or> (y,x) \<in> (tree_edges s)\<^sup>+"
  proof -
    from x obtain px where px: "path (tree_edges s) x px v" and "px \<noteq> []"
      using trancl_is_path by metis
    from y obtain py where py: "path (tree_edges s) y py v" and "py \<noteq> []"
      using trancl_is_path by metis

    from \<open>px \<noteq> []\<close> \<open>py \<noteq> []\<close> px py
    show ?thesis
    proof (induction arbitrary: v rule: rev_nonempty_induct2')
      case (single) hence "(x,v) \<in> tree_edges s" "(y,v) \<in> tree_edges s" 
        by (simp_all add: path_simps)
      with tree_eq_rule have "x=y" by simp
      with \<open>x\<noteq>y\<close> show ?case by contradiction
    next
      case (snocl a as) hence "(y,v) \<in> tree_edges s" by (simp add: path_simps)
      moreover from snocl have "path (tree_edges s) x as a" "(a,v) \<in> tree_edges s" 
        by (simp_all add: path_simps)
      ultimately have "path (tree_edges s) x as y"
        using tree_eq_rule
        by auto
      with path_is_trancl \<open>as \<noteq> []\<close> show ?case by metis
    next
      case (snocr _ a as) hence "(x,v) \<in> tree_edges s" by (simp add: path_simps)
      moreover from snocr have "path (tree_edges s) y as a" "(a,v) \<in> tree_edges s" 
        by (simp_all add: path_simps)
      ultimately have "path (tree_edges s) y as x"
        using tree_eq_rule
        by auto
      with path_is_trancl \<open>as \<noteq> []\<close> show ?case by metis
    next
      case (snoclr a as b bs) hence 
        "path (tree_edges s) x as a" "(a,v) \<in> tree_edges s"
        "path (tree_edges s) y bs b" "(b,v) \<in> tree_edges s"
        by (simp_all add: path_simps)
      moreover hence "a=b"  using tree_eq_rule by simp
      ultimately show ?thesis using snoclr.IH by metis
    qed
  qed

  lemma tree_subpath:
    assumes "(x,v) \<in> (tree_edges s)\<^sup>+"
    and "(y,v) \<in> (tree_edges s)\<^sup>+"
    and \<delta>: "\<delta> s x < \<delta> s y"
    shows "(x,y) \<in> (tree_edges s)\<^sup>+"
  proof -
    from \<delta> have "x \<noteq> y" by auto
    with assms tree_subpath' have "(x,y) \<in> (tree_edges s)\<^sup>+ \<or> (y,x) \<in> (tree_edges s)\<^sup>+" 
      by simp
    moreover from \<delta> tree_path_disc have "(y,x) \<notin> (tree_edges s)\<^sup>+" by force
    ultimately show ?thesis by simp
  qed

  lemma on_stack_is_tree_path:
    assumes x: "x \<in> set (stack s)"
    and y: "y \<in> set (stack s)"
    and \<delta>: "\<delta> s x < \<delta> s y"
    shows "(x,y) \<in> (tree_edges s)\<^sup>+"
  proof -
    from x obtain i where i: "stack s ! i = x" "i < length (stack s)"
      by (metis in_set_conv_nth)

    from y obtain j where j: "stack s ! j = y" "j < length (stack s)"
      by (metis in_set_conv_nth)
    
    with i \<delta> stack_nth_order have "j < i" by force
    
    from x have ne[simp]: "stack s \<noteq> []" by auto

    from \<open>j<i\<close> have "x \<in> set (tl (stack s))"
      using nth_mem nth_tl[OF ne, of "i - 1"] i
      by auto
    with tl_stack_hd_tree_path have 
      x_path: "(x, hd (stack s)) \<in> (tree_edges s)\<^sup>+" 
      by simp

    then show ?thesis
    proof (cases "j=0")
      case True with j have "hd (stack s) = y" by (metis hd_conv_nth ne)
      with x_path show ?thesis by simp
    next
      case False hence "y \<in> set (tl (stack s))"
        using nth_mem nth_tl[OF ne, of "j - 1"] j
        by auto
      with tl_stack_hd_tree_path have "(y, hd (stack s)) \<in> (tree_edges s)\<^sup>+" 
        by simp
      with x_path \<delta> show ?thesis
        using tree_subpath
        by metis
    qed
  qed

  lemma hd_stack_tree_path_finished:
    assumes "stack s \<noteq> []"
    assumes "(hd (stack s), v) \<in> (tree_edges s)\<^sup>+"
    shows "v \<in> dom (finished s)"
  proof (cases "v \<in> set (stack s)")
    case True
    from assms no_loop_in_tree have "hd (stack s) \<noteq> v" by auto
    with True have "v \<in> set (tl (stack s))" by (cases "stack s") auto
    with tl_stack_hd_tree_path assms have "(hd (stack s), hd (stack s)) \<in> (tree_edges s)\<^sup>+" by (metis trancl_trans)
    with no_loop_in_tree show ?thesis by contradiction
  next
    case False
    from assms obtain x where "(x,v) \<in> tree_edges s" by (metis tranclE)
    with tree_edge_imp_discovered have "v \<in> dom (discovered s)" by blast
    with False show ?thesis by (simp add: stack_set_def)
  qed

  lemma tree_edge_impl_parenthesis:
    assumes t: "(v,w) \<in> tree_edges s"
    and f: "v \<in> dom (finished s)"
    shows "w \<in> dom (finished s) 
      \<and> \<delta> s v < \<delta> s w
      \<and> \<phi> s w < \<phi> s v "
  proof -
    from tree_edge_disc_lt_fin assms have "\<delta> s w < \<phi> s v" by simp
    with f tree_edge_imp_discovered[OF t] tree_edge_disc[OF t]
    show ?thesis
      using parenthesis_contained
      by metis
  qed

  lemma tree_path_impl_parenthesis:
    assumes "(v,w) \<in> (tree_edges s)\<^sup>+"
    and "v \<in> dom (finished s)"
    shows "w \<in> dom (finished s) 
      \<and> \<delta> s v < \<delta> s w
      \<and> \<phi> s w < \<phi> s v "
    using assms
    by (auto elim!: trancl_induct dest: tree_edge_impl_parenthesis)

  lemma nc_reachable_v0_parenthesis:
    assumes C: "\<not> cond s" "\<not> is_break param s"
    and v: "v \<in> reachable" "v \<notin> V0"
    obtains v0 where "v0 \<in> V0"
                 and "\<delta> s v0 < \<delta> s v \<and> \<phi> s v < \<phi> s v0 "
  proof -
    from nc_discovered_eq_reachable[OF C] discovered_iff_tree_path v
    obtain v0 where "v0 \<in> V0" and
      "(v0,v) \<in> (tree_edges s)\<^sup>+" 
      by auto
    moreover with nc_V0_finished[OF C] have "v0 \<in> dom (finished s)" 
      by auto
    ultimately show ?thesis
      using tree_path_impl_parenthesis that[OF \<open>v0 \<in> V0\<close>]
      by simp
  qed

end end

context param_DFS begin context begin interpretation timing_syntax .

  definition paren_imp_tree_reach where
    "paren_imp_tree_reach s \<equiv> \<forall>v \<in> dom (discovered s). \<forall>w \<in> dom (finished s). 
        \<delta> s v < \<delta> s w \<and> (v \<notin> dom (finished s) \<or> \<phi> s v > \<phi> s w) 
               \<longrightarrow> (v,w) \<in> (tree_edges s)\<^sup>+"

  lemma paren_imp_tree_reach:
    "is_invar paren_imp_tree_reach"
    unfolding paren_imp_tree_reach_def[abs_def]
  proof (induct rule: is_invarI)
    case (discover s s' u v) 
    hence EQ[simp]: "tree_edges s' = insert (hd (stack s), v) (tree_edges s)"
                    "finished s' = finished s"
                    "discovered s' = (discovered s)(v \<mapsto> counter s)"
      by simp_all

    from discover interpret DFS_invar where s=s by simp
    from discover have NE[simp]: "stack s \<noteq> []" by (simp add: cond_alt)
    
    show ?case
    proof (intro ballI impI)
      fix a b
      assume F:"a \<in> dom (discovered s')" "b \<in> dom (finished s')"
        and D: "\<delta> s' a < \<delta> s' b \<and> (a \<notin> dom (finished s') \<or> \<phi> s' a > \<phi> s' b)"
        
      from F finished_discovered discover have "b \<noteq> v" by auto
      show "(a,b) \<in> (tree_edges s')\<^sup>+"
      proof (cases "a = v")
        case True with D \<open>b\<noteq>v\<close> have "counter s < \<delta> s b" by simp
        also from F have "b \<in> dom (discovered s)" 
          using finished_discovered by auto
        with timing_less_counter have "\<delta> s b < counter s" by simp
        finally have False .
        thus ?thesis ..
      next
        case False with \<open>b\<noteq>v\<close> F D discover have "(a,b) \<in> (tree_edges s)\<^sup>+" by simp
        thus ?thesis by (auto intro: trancl_mono_mp)
      qed
    qed
  next
    case (finish s s' u) 
    hence EQ[simp]: "tree_edges s' = tree_edges s"
                    "finished s' = (finished s)(hd (stack s) \<mapsto> counter s)"
                    "discovered s' = discovered s"
                    "stack s' = tl (stack s)"
      by simp_all

    from finish interpret DFS_invar where s=s by simp
    from finish have NE[simp]: "stack s \<noteq> []" by (simp add: cond_alt)

    show ?case
    proof (intro ballI impI)
      fix a b
      assume F: "a \<in> dom (discovered s')" "b \<in> dom (finished s')"
        and paren: "\<delta> s' a < \<delta> s' b \<and> (a \<notin> dom (finished s') \<or> \<phi> s' a > \<phi> s' b)"
      hence "a \<noteq> b" by auto
      
      show "(a,b) \<in> (tree_edges s')\<^sup>+"
      proof (cases "b = hd (stack s)")
        case True hence \<phi>b: "\<phi> s' b = counter s" by simp
        have "a \<in> set (stack s)"
          unfolding stack_set_def
        proof
          from F show "a \<in> dom (discovered s)" by simp
          from True \<open>a\<noteq>b\<close> \<phi>b paren have "a \<in> dom (finished s) \<longrightarrow> \<phi> s a > counter s" by simp
          with timing_less_counter show "a \<notin> dom (finished s)" by force
        qed 
        with paren True on_stack_is_tree_path have "(a,b) \<in> (tree_edges s)\<^sup>+" by auto
        thus ?thesis by (auto intro: trancl_mono_mp)
      next
        case False note b_not_hd = this
        show ?thesis
        proof (cases "a = hd (stack s)")
          case False with b_not_hd F paren finish show ?thesis by simp
        next
          case True with paren b_not_hd F have 
            "a \<in> dom (discovered s)" "b \<in> dom (finished s)"  "\<delta> s a < \<delta> s b"  
            by simp_all
          moreover from True stack_not_finished have "a \<notin> dom (finished s)" 
            by simp
          ultimately show ?thesis by (simp add: finish)
        qed
      qed
    qed  
  next
    case (new_root s s' v0) then interpret DFS_invar where s=s by simp
    from new_root finished_discovered have "v0 \<notin> dom (finished s)" by auto
    moreover note timing_less_counter finished_discovered
    ultimately show ?case using new_root by clarsimp force
  qed simp_all
end end

context DFS_invar begin context begin interpretation timing_syntax .

  lemmas s_paren_imp_tree_reach =
    paren_imp_tree_reach[THEN make_invar_thm]
  
  lemma parenthesis_impl_tree_path_not_finished:
    assumes "v \<in> dom (discovered s)"
    and "w \<in> dom (finished s)"
    and "\<delta> s v < \<delta> s w"
    and "v \<notin> dom (finished s)"
    shows "(v,w) \<in> (tree_edges s)\<^sup>+"
    using s_paren_imp_tree_reach assms
    by (auto simp add: paren_imp_tree_reach_def)

  lemma parenthesis_impl_tree_path:
    assumes "v \<in> dom (finished s)" "w \<in> dom (finished s)"
    and "\<delta> s v < \<delta> s w" "\<phi> s v > \<phi> s w"
    shows "(v,w) \<in> (tree_edges s)\<^sup>+"
  proof -
    from assms(1) have "v \<in> dom (discovered s)"
      using finished_discovered by blast
    with assms show ?thesis
      using s_paren_imp_tree_reach assms
      by (auto simp add: paren_imp_tree_reach_def)
  qed

  lemma tree_path_iff_parenthesis:
    assumes "v \<in> dom (finished s)" "w \<in> dom (finished s)"
    shows "(v,w) \<in> (tree_edges s)\<^sup>+ \<longleftrightarrow> \<delta> s v < \<delta> s w \<and> \<phi> s v > \<phi> s w"
    using assms
    by (metis parenthesis_impl_tree_path tree_path_impl_parenthesis) 

  lemma no_pending_succ_impl_path_in_tree:
    assumes v: "v \<in> dom (discovered s)" "pending s `` {v} = {}"
    and w: "w \<in> succ v"
    and \<delta>: "\<delta> s v < \<delta> s w"
    shows "(v,w) \<in> (tree_edges s)\<^sup>+"
  proof (cases "v \<in> dom (finished s)")
    case True 
    with assms assms have "\<delta> s w < \<phi> s v" "w \<in> dom (discovered s)"
      using finished_succ_fin finished_imp_succ_discovered 
      by simp_all
    with True \<delta> show ?thesis
      using parenthesis_contained parenthesis_impl_tree_path
      by blast
  next
    case False
    show ?thesis
    proof (cases "w \<in> dom (finished s)")
      case True with False v \<delta> show ?thesis by (simp add: parenthesis_impl_tree_path_not_finished)
    next
      case False with \<open>v \<notin> dom (finished s)\<close> no_pending_imp_succ_discovered v w have 
        "v \<in> set (stack s)" "w \<in> set (stack s)" 
        by (simp_all add: stack_set_def)
      with on_stack_is_tree_path \<delta> show ?thesis by simp
    qed
  qed

  lemma finished_succ_impl_path_in_tree:
    assumes f:  "v \<in> dom (finished s)"
    and s: "w \<in> succ v"
    and \<delta>: "\<delta> s v < \<delta> s w"
    shows "(v,w) \<in> (tree_edges s)\<^sup>+"
    using no_pending_succ_impl_path_in_tree finished_no_pending finished_discovered
    using assms
    by blast
end end

subsubsection \<open>Properties of Cross Edges\<close>
(* Cross Edges *)
context param_DFS begin context begin interpretation timing_syntax .

  lemma i_cross_edges_finished: "is_invar (\<lambda>s. \<forall>(u,v)\<in>cross_edges s. 
    v \<in> dom (finished s) \<and> (u \<in> dom (finished s) \<longrightarrow> \<phi> s v < \<phi> s u))"
  proof (induction rule: is_invarI_full)
    case (finish s s' u e)
    interpret DFS_invar G param s by fact
    from finish stack_not_finished have "u \<notin> dom (finished s)" by auto
    with finish show ?case by (auto intro: timing_less_counter)
  next
    case (cross_edge s s' u v e)
    interpret DFS_invar G param s by fact
    from cross_edge stack_not_finished have "u \<notin> dom (finished s)" by auto
    with cross_edge show ?case by (auto intro: timing_less_counter)
  qed simp_all

end end

context DFS_invar begin context begin interpretation timing_syntax .
  lemmas cross_edges_finished 
    = i_cross_edges_finished[THEN make_invar_thm]

  lemma cross_edges_target_finished: 
    "(u,v)\<in>cross_edges s \<Longrightarrow> v \<in> dom (finished s)" 
    using cross_edges_finished by auto

  lemma cross_edges_finished_decr: 
    "\<lbrakk>(u,v)\<in>cross_edges s; u\<in>dom (finished s)\<rbrakk> \<Longrightarrow> \<phi> s v < \<phi> s u" 
    using cross_edges_finished by auto

  lemma cross_edge_unequal:
    assumes cross: "(v,w) \<in> cross_edges s"
    shows "v \<noteq> w"
  proof -
    from cross_edges_target_finished[OF cross] have 
      w_fin: "w \<in> dom (finished s)" .

    show ?thesis
    proof (cases "v \<in> dom (finished s)")
      case True with cross_edges_finished_decr[OF cross] 
      show ?thesis by force
    next
      case False with w_fin show ?thesis by force
    qed
  qed 
end end


subsubsection \<open>Properties of Back Edges\<close>
(* Back Edges *)
context param_DFS begin context begin interpretation timing_syntax .
  
  lemma i_back_edge_impl_tree_path:
    "is_invar (\<lambda>s. \<forall>(v,w) \<in> back_edges s. (w,v) \<in> (tree_edges s)\<^sup>+ \<or> w = v)"
  proof (induct rule: is_invarI_full)
    case (back_edge s s' u v) then interpret DFS_invar where s=s by simp

    from back_edge have st: "v \<in> set (stack s)" "u \<in> set (stack s)"
      using stack_set_def
      by auto
   
    have "(v,u) \<in> (tree_edges s)\<^sup>+ \<or> u = v"
    proof (rule disjCI)
      assume "u \<noteq> v"
      with st back_edge have "v \<in> set (tl (stack s))" by (metis not_hd_in_tl)
      with tl_lt_stack_hd_discover st back_edge have "\<delta> s v < \<delta> s u" by simp
      with on_stack_is_tree_path st show "(v,u) \<in> (tree_edges s)\<^sup>+" by simp
    qed
    with back_edge show ?case by auto
  next
    case discover thus ?case using trancl_sub_insert_trancl by force
  qed simp_all

end end

context DFS_invar begin context begin interpretation timing_syntax .

  lemma back_edge_impl_tree_path:
    "\<lbrakk>(v,w) \<in> back_edges s; v \<noteq> w\<rbrakk> \<Longrightarrow> (w,v) \<in> (tree_edges s)\<^sup>+"
    using i_back_edge_impl_tree_path[THEN make_invar_thm]
    by blast

  lemma back_edge_disc:
    assumes "(v,w) \<in> back_edges s"
    shows "\<delta> s w \<le> \<delta> s v"
  proof cases
    assume "v\<noteq>w" 
    with assms back_edge_impl_tree_path have "(w,v) \<in> (tree_edges s)\<^sup>+" by simp
    with tree_path_disc show ?thesis by force
  qed simp

  lemma back_edges_tree_disjoint:
    "back_edges s \<inter> tree_edges s = {}"
    using back_edge_disc tree_edge_disc
    by force

  lemma back_edges_tree_pathes_disjoint:
    "back_edges s \<inter> (tree_edges s)\<^sup>+ = {}"
    using back_edge_disc tree_path_disc
    by force

  lemma back_edge_finished:
    assumes "(v,w) \<in> back_edges s"
    and "w \<in> dom (finished s)"
    shows "v \<in> dom (finished s) \<and> \<phi> s v \<le> \<phi> s w"
  proof (cases "v=w")
    case True with assms show ?thesis by simp
  next
    case False with back_edge_impl_tree_path assms have "(w,v) \<in> (tree_edges s)\<^sup>+" by simp
    with tree_path_impl_parenthesis assms show ?thesis by fastforce
  qed

end end

context param_DFS begin context begin interpretation timing_syntax .
  (* The lemma should probably replaced by:
     is_invar (\<lambda>s. \<forall>(v,w) \<in> (tree_edges s)\<^sup>+. v \<in> succ w \<longrightarrow> (w,v) \<in> back_edges s \<or> (w,v) \<in> pending s)
  *)
  lemma i_disc_imp_back_edge_or_pending:
    "is_invar (\<lambda>s. \<forall>(v,w) \<in> E. 
        v \<in> dom (discovered s) \<and> w \<in> dom (discovered s)
      \<and> \<delta> s v \<ge> \<delta> s w
      \<and> (w \<in> dom (finished s) \<longrightarrow> v \<in> dom (finished s) \<and> \<phi> s w \<ge> \<phi> s v)
      \<longrightarrow> (v,w) \<in> back_edges s \<or> (v,w) \<in> pending s)"
  proof (induct rule: is_invarI_full)
    case (cross_edge s s' u v) then interpret DFS_invar where s=s by simp
    from cross_edge stack_not_finished[of u] have "u \<notin> dom (finished s)"
      using hd_in_set
      by (auto simp add: cond_alt)
    with cross_edge show ?case by auto
  next
    case (finish s s' u v) then interpret DFS_invar where s=s by simp

    from finish have 
      IH: "\<And>v w. \<lbrakk>w \<in> succ v; v \<in> dom (discovered s); w \<in> dom (discovered s); 
                  \<delta> s w \<le> \<delta> s v;
                  (w \<in> dom (finished s) \<Longrightarrow> v \<in> dom (finished s) \<and> \<phi> s v \<le> \<phi> s w)\<rbrakk>
                 \<Longrightarrow> (v, w) \<in> back_edges s \<or> (v, w) \<in> pending s" 
      by blast

    from finish have ne[simp]: "stack s \<noteq> []"
                 and p[simp]: "pending s `` {hd (stack s)} = {}"
      by (simp_all)

    from hd_in_set[OF ne] have disc: "hd (stack s) \<in> dom (discovered s)" 
                            and not_fin: "hd (stack s) \<notin> dom (finished s)"
      using stack_discovered stack_not_finished
      by blast+

    {
      fix w
      assume w: "w \<in> succ (hd (stack s))" "w \<noteq> hd (stack s)" "w \<in> dom (discovered s)"
        and f: "w \<in> dom (finished s) \<longrightarrow> counter s \<le> \<phi> s w"
        and \<delta>: "\<delta> s w \<le> \<delta> s (hd (stack s))"

      with timing_less_counter have "w \<notin> dom (finished s)" by force
      with finish w \<delta> disc have "(hd (stack s), w) \<in> back_edges s" by blast
    }

    moreover
    {
      fix w
      assume "hd (stack s) \<in> succ w" "w \<noteq> hd (stack s)"
      and "w \<in> dom (finished s)" "\<delta> s (hd (stack s)) \<le> \<delta> s w"
      with IH[of "hd (stack s)" w] disc not_fin have
        "(w, hd (stack s)) \<in> back_edges s"
        using finished_discovered finished_no_pending[of w]
        by blast
    }

    ultimately show ?case
      using finish
      by clarsimp auto
  next
    case (discover s s' u v) then interpret DFS_invar where s=s by simp

    from discover show ?case 
      using timing_less_counter
      by clarsimp fastforce
  next
    case (new_root s s' v0) then interpret DFS_invar where s=s by simp

    from new_root empty_stack_imp_empty_pending have "pending s = {}" by simp
    with new_root show ?case 
      using timing_less_counter
      by clarsimp fastforce
  qed auto
end end

context DFS_invar begin context begin interpretation timing_syntax .

  lemma disc_imp_back_edge_or_pending:
    "\<lbrakk>w \<in> succ v; v \<in> dom (discovered s); w \<in> dom (discovered s); \<delta> s w \<le> \<delta> s v;
      (w \<in> dom (finished s) \<Longrightarrow> v \<in> dom (finished s) \<and> \<phi> s v \<le> \<phi> s w)\<rbrakk>
     \<Longrightarrow> (v, w) \<in> back_edges s \<or> (v, w) \<in> pending s"
    using i_disc_imp_back_edge_or_pending[THEN make_invar_thm]
    by blast

  lemma finished_imp_back_edge:
    "\<lbrakk>w \<in> succ v; v \<in> dom (finished s); w \<in> dom (finished s); 
      \<delta> s w \<le> \<delta> s v; \<phi> s v \<le> \<phi> s w\<rbrakk>
     \<Longrightarrow> (v, w) \<in> back_edges s"
    using disc_imp_back_edge_or_pending finished_discovered finished_no_pending
    by fast

  lemma finished_not_finished_imp_back_edge:
    "\<lbrakk>w \<in> succ v; v \<in> dom (finished s); w \<in> dom (discovered s);
      w \<notin> dom (finished s);
      \<delta> s w \<le> \<delta> s v\<rbrakk>
     \<Longrightarrow> (v, w) \<in> back_edges s"
    using disc_imp_back_edge_or_pending finished_discovered finished_no_pending
    by fast

  lemma finished_self_loop_in_back_edges:
    assumes "v \<in> dom (finished s)"
    and "(v,v) \<in> E"
    shows "(v,v) \<in> back_edges s"
    using assms
    using finished_imp_back_edge
    by blast
end end

(* Back edges and Cycles *)

context DFS_invar begin 

  context begin interpretation timing_syntax .
    (* Cross and tree_edges edges are always acyclic *)
    lemma tree_cross_acyclic:
      "acyclic (tree_edges s \<union> cross_edges s)" (is "acyclic ?E")
    proof (rule ccontr)
      {
        fix u v
        assume *: "u \<in> dom (finished s)" and "(u,v) \<in> ?E\<^sup>+"
        from this(2) have "\<phi> s v < \<phi> s u \<and> v \<in> dom (finished s)"
        proof induct
          case base thus ?case 
            by (metis Un_iff * cross_edges_finished_decr cross_edges_target_finished tree_edge_impl_parenthesis)
        next
          case (step v w)
          hence "\<phi> s w < \<phi> s v \<and> w \<in> dom (finished s)"
            by (metis Un_iff cross_edges_finished_decr cross_edges_target_finished tree_edge_impl_parenthesis)
          with step show ?case by auto
        qed
      } note aux = this

      assume "\<not> acyclic ?E"
      then obtain u where path: "(u,u) \<in> ?E\<^sup>+" by (auto simp add: acyclic_def)
      show False
      proof cases
        assume "u \<in> dom (finished s)" 
        with aux path show False by blast
      next
        assume *: "u \<notin> dom (finished s)"
        moreover 
        from no_loop_in_tree have "(u,u) \<notin> (tree_edges s)\<^sup>+" .
        with trancl_union_outside[OF path] obtain x y where "(u,x) \<in> ?E\<^sup>*" "(x,y) \<in> cross_edges s" "(y,u) \<in> ?E\<^sup>*" by auto
        with cross_edges_target_finished have "y \<in> dom (finished s)" by simp
        moreover with * \<open>(y,u) \<in> ?E\<^sup>*\<close> have "(y,u) \<in> ?E\<^sup>+" by (auto simp add: rtrancl_eq_or_trancl)
        ultimately show False by (metis aux)
      qed
    qed
  end

  lemma cycle_contains_back_edge:
    assumes cycle: "(u,u) \<in> (edges s)\<^sup>+"
    shows "\<exists>v w. (u,v) \<in> (edges s)\<^sup>* \<and> (v,w) \<in> back_edges s \<and> (w,u) \<in> (edges s)\<^sup>*"
  proof -
    from tree_cross_acyclic have "(u,u) \<notin> (tree_edges s \<union> cross_edges s)\<^sup>+" by (simp add: acyclic_def)
    with trancl_union_outside[OF cycle] show ?thesis .
  qed

  lemma cycle_needs_back_edge:
    assumes "back_edges s = {}"
    shows "acyclic (edges s)"
  proof (rule ccontr)
    assume "\<not> acyclic (edges s)"
    then obtain u where "(u,u) \<in> (edges s)\<^sup>+" by (auto simp: acyclic_def)
    with assms have "(u,u) \<in> (tree_edges s \<union> cross_edges s)\<^sup>+" by auto
    with tree_cross_acyclic show False by (simp add: acyclic_def)
  qed

  lemma back_edge_closes_cycle:
    assumes "back_edges s \<noteq> {}"
    shows "\<not> acyclic (edges s)"
  proof -
    from assms obtain v w where be: "(v,w) \<in> back_edges s" by auto
    hence "(w,w) \<in> (edges s)\<^sup>+"
    proof (cases "v=w")
      case False 
      with be back_edge_impl_tree_path have "(w,v) \<in> (tree_edges s)\<^sup>+" by simp
      hence "(w,v) \<in> (edges s)\<^sup>+" by (blast intro: trancl_mono_mp)
      also from be have "(v,w) \<in> edges s" by simp
      finally show ?thesis .
    qed auto
    thus ?thesis by (auto simp add: acyclic_def)
  qed

  lemma back_edge_closes_reachable_cycle:
    "back_edges s \<noteq> {} \<Longrightarrow> \<not> acyclic (E \<inter> reachable \<times> UNIV)"
    by (metis back_edge_closes_cycle edges_ss_reachable_edges cyclic_subset)

  lemma cycle_iff_back_edges:
    "acyclic (edges s) \<longleftrightarrow> back_edges s = {}"
  by (metis back_edge_closes_cycle cycle_needs_back_edge)
end 


subsection \<open>White Path Theorem\<close>

context DFS begin
context begin interpretation timing_syntax .

  definition white_path where
    "white_path s x y \<equiv> x\<noteq>y 
       \<longrightarrow> (\<exists>p. path E x p y \<and> 
               (\<delta> s x < \<delta> s y \<and> (\<forall> v \<in> set (tl p). \<delta> s x < \<delta> s v)))"

  lemma white_path:
    "it_dfs \<le> SPEC(\<lambda>s. \<forall>x \<in> reachable. \<forall>y \<in> reachable. \<not> is_break param s \<longrightarrow> 
            white_path s x y \<longleftrightarrow> (x,y) \<in> (tree_edges s)\<^sup>*)"
  proof (rule it_dfs_SPEC, intro ballI impI)
    fix s x y
    assume DI: "DFS_invar G param s"
      and C: "\<not> cond s" "\<not> is_break param s"
      and reach: "x \<in> reachable" "y \<in> reachable"

    from DI interpret DFS_invar where s=s .

    note fin_eq_reach = nc_finished_eq_reachable[OF C]

    show "white_path s x y \<longleftrightarrow> (x,y) \<in> (tree_edges s)\<^sup>*"
    proof (cases "x=y")
      case True thus ?thesis by (simp add: white_path_def)
    next
      case False
      
      show ?thesis
      proof
        assume "(x,y) \<in> (tree_edges s)\<^sup>*"
        with \<open>x\<noteq>y\<close> have T: "(x,y) \<in> (tree_edges s)\<^sup>+" by (metis rtranclD)
        then obtain p where P: "path (tree_edges s) x p y" by (metis trancl_is_path)
        with tree_edges_ssE have "path E x p y" using path_mono[where E="tree_edges s"] 
          by simp
        moreover 
        from P have "\<delta> s x < \<delta> s y \<and> (\<forall> v \<in> set (tl p). \<delta> s x < \<delta> s v)"
          using \<open>x\<noteq>y\<close>
        proof (induct rule: path_tl_induct)
          case (single u) thus ?case by (fact tree_edge_disc)
        next
          case (step u v) note \<open>\<delta> s x < \<delta> s u\<close>
          also from step have "\<delta> s u < \<delta> s v" by (metis tree_edge_disc)
          finally show ?case .
        qed
        ultimately show "white_path s x y"
          by (auto simp add: \<open>x\<noteq>y\<close> white_path_def)
      next
        assume "white_path s x y"
        with \<open>x\<noteq>y\<close> obtain p where 
            P:"path E x p y" and
            white: "\<delta> s x < \<delta> s y \<and> (\<forall> v \<in> set (tl p). \<delta> s x < \<delta> s v)"
          unfolding white_path_def
          by blast
        hence "p \<noteq> []" by auto
        thus "(x,y) \<in> (tree_edges s)\<^sup>*" using P white reach(2)
        proof (induction p arbitrary: y rule: rev_nonempty_induct)
          case single hence "y \<in> succ x" by (simp add: path_cons_conv)
          with reach single show ?case 
            using fin_eq_reach finished_succ_impl_path_in_tree[of x y] 
            by simp
        next
          case (snoc u us) hence "path E x us u" by (simp add: path_append_conv)
          moreover hence "(x,u) \<in> E\<^sup>*" by (simp add: path_is_rtrancl)
          with reach have ureach: "u \<in> reachable" 
            by (metis rtrancl_image_advance_rtrancl) 
          moreover from snoc have "\<delta> s x < \<delta> s u" "(\<forall>v\<in>set (tl us). \<delta> s x < \<delta> s v)" 
            by simp_all
          ultimately have x_u: "(x,u) \<in> (tree_edges s)\<^sup>*" by (metis snoc.IH)
            
          from snoc have "y \<in> succ u" by (simp add: path_append_conv)
          from snoc(5) fin_eq_reach finished_discovered have 
            y_f_d: "y \<in> dom (finished s)" "y \<in> dom (discovered s)"
            by auto
            
          from \<open>y \<in> succ u\<close> ureach fin_eq_reach have "\<delta> s y < \<phi> s u" 
            using finished_succ_fin by simp
          also from \<open>\<delta> s x < \<delta> s u\<close> have "x \<noteq> u" by auto
          with x_u have "(x,u) \<in> (tree_edges s)\<^sup>+" by (metis rtrancl_eq_or_trancl)
          with fin_eq_reach reach have "\<phi> s u < \<phi> s x" 
            using tree_path_impl_parenthesis
            by simp
          finally have "\<phi> s y < \<phi> s x" 
            using reach fin_eq_reach y_f_d snoc
            using parenthesis_contained
            by blast
          hence "(x,y) \<in> (tree_edges s)\<^sup>+"
            using reach fin_eq_reach y_f_d snoc
            using parenthesis_impl_tree_path
            by blast
          thus ?case by auto
        qed
      qed
    qed
  qed
end end


end
